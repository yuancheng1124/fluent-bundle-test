//! `FluentBundle` is a collection of localization messages in Fluent.
//!
//! It stores a list of messages in a single locale which can reference one another, use the same
//! internationalization formatters, functions, environmental variables and are expected to be used
//! together.

#[macro_use]
extern crate rental;
#[macro_use]
extern crate failure_derive;

use std::f32;
use std::num::ParseFloatError;
use std::str::FromStr;
use std::cell::RefCell;
use std::collections::hash_map::DefaultHasher;
use std::collections::hash_map::{Entry as HashEntry, HashMap};
use std::hash::{Hash, Hasher};

use fluent_locale::{negotiate_languages, NegotiationStrategy};
use fluent_syntax::ast;
use fluent_syntax::parser::parse;
use fluent_syntax::parser::ParserError;
use fluent_syntax::unicode::unescape_unicode;

use intl_pluralrules::{IntlPluralRules, PluralRuleType, PluralCategory};
use wasm_bindgen::prelude::*;


///
/// bundle.rs
///
#[derive(Debug, PartialEq)]
pub struct Message {
    pub value: Option<String>,
    pub attributes: HashMap<String, String>,
}

/// A collection of localization messages for a single locale, which are meant
/// to be used together in a single view, widget or any other UI abstraction.
///
/// # Examples
///
/// ```
/// use fluent_bundle::{FluentBundle, FluentResource, FluentValue};
/// use std::collections::HashMap;
///
/// let ftl_string = String::from("intro = Welcome, { $name }.");
/// let resource = FluentResource::try_new(ftl_string)
///     .expect("Could not parse an FTL string.");
///
/// let mut bundle = FluentBundle::new(&["en-US"]);
/// bundle.add_resource(&resource)
///     .expect("Failed to add FTL resources to the bundle.");
///
/// let mut args = HashMap::new();
/// args.insert("name", FluentValue::from("Rustacean"));
///
/// let (value, _) = bundle.format("intro", Some(&args))
///     .expect("Failed to format a message.");
/// assert_eq!(&value, "Welcome, Rustacean.");
///
/// ```
///
/// # `FluentBundle` Life Cycle
///
/// To create a bundle, call [`FluentBundle::new`] with a locale list that represents the best
/// possible fallback chain for a given locale. The simplest case is a one-locale list.
///
/// Next, call [`add_resource`] one or more times, supplying translations in the FTL syntax. The
/// `FluentBundle` instance is now ready to be used for localization.
///
/// To format a translation, call [`format`] with the path of a message or attribute in order to
/// retrieve the translated string. Alternately, [`compound`] provides a convenient way of
/// formatting all attributes of a message at once.
///
/// The result of `format` is an [`Option<T>`] wrapping a `(String, Vec<FluentError>)`. On success,
/// the string is a formatted value that should be displayed in the UI. It is
/// recommended to treat the result as opaque from the perspective of the program and use it only
/// to display localized messages. Do not examine it or alter in any way before displaying.  This
/// is a general good practice as far as all internationalization operations are concerned.
///
///
/// # Locale Fallback Chain
///
/// `FluentBundle` stores messages in a single locale, but keeps a locale fallback chain for the
/// purpose of language negotiation with i18n formatters. For instance, if date and time formatting
/// are not available in the first locale, `FluentBundle` will use its `locales` fallback chain
/// to negotiate a sensible fallback for date and time formatting.
///
/// [`add_resource`]: ./struct.FluentBundle.html#method.add_resource
/// [`FluentBundle::new`]: ./struct.FluentBundle.html#method.new
/// [`fluent::bundle::Message`]: ./struct.FluentBundle.html#method.new
/// [`format`]: ./struct.FluentBundle.html#method.format
/// [`compound`]: ./struct.FluentBundle.html#method.compound
/// [`add_resource`]: ./struct.FluentBundle.html#method.add_resource
/// [`Option<T>`]: http://doc.rust-lang.org/std/option/enum.Option.html
pub struct FluentBundle<'bundle> {
    pub locales: Vec<String>,
    pub entries: HashMap<String, Entry<'bundle>>,
    pub plural_rules: IntlPluralRules,
}

impl<'bundle> FluentBundle<'bundle> {
    /// Constructs a FluentBundle. `locales` is the fallback chain of locales
    /// to use for formatters like date and time. `locales` does not influence
    /// message selection.
    ///
    /// # Examples
    ///
    /// ```
    /// use fluent_bundle::FluentBundle;
    ///
    /// let mut bundle = FluentBundle::new(&["en-US"]);
    /// ```
    ///
    /// # Errors
    ///
    /// This will panic if no formatters can be found for the locales.
    pub fn new<'a, S: ToString>(locales: &'a [S]) -> FluentBundle<'bundle> {
        let locales = locales
            .iter()
            .map(std::string::ToString::to_string)
            .collect::<Vec<_>>();
        let pr_locale = negotiate_languages(
            &locales,
            IntlPluralRules::get_locales(PluralRuleType::CARDINAL),
            Some("en"),
            &NegotiationStrategy::Lookup,
        )[0]
        .to_owned();

        let pr = IntlPluralRules::create(&pr_locale, PluralRuleType::CARDINAL)
            .expect("Failed to initialize PluralRules.");
        FluentBundle {
            locales,
            entries: HashMap::new(),
            plural_rules: pr,
        }
    }

    /// Returns true if this bundle contains a message with the given id.
    ///
    /// # Examples
    ///
    /// ```
    /// use fluent_bundle::{FluentBundle, FluentResource};
    ///
    /// let ftl_string = String::from("hello = Hi!");
    /// let resource = FluentResource::try_new(ftl_string)
    ///     .expect("Failed to parse an FTL string.");
    /// let mut bundle = FluentBundle::new(&["en-US"]);
    /// bundle.add_resource(&resource)
    ///     .expect("Failed to add FTL resources to the bundle.");
    /// assert_eq!(true, bundle.has_message("hello"));
    ///
    /// ```
    pub fn has_message(&self, id: &str) -> bool {
        self.entries.get_message(id).is_some()
    }

    /// Makes the provided rust function available to messages with the name `id`. See
    /// the [FTL syntax guide] to learn how these are used in messages.
    ///
    /// FTL functions accept both positional and named args. The rust function you
    /// provide therefore has two parameters: a slice of values for the positional
    /// args, and a HashMap of values for named args.
    ///
    /// # Examples
    ///
    /// ```
    /// use fluent_bundle::{FluentBundle, FluentResource, FluentValue};
    ///
    /// let ftl_string = String::from("length = { STRLEN(\"12345\") }");
    /// let resource = FluentResource::try_new(ftl_string)
    ///     .expect("Could not parse an FTL string.");
    /// let mut bundle = FluentBundle::new(&["en-US"]);
    /// bundle.add_resource(&resource)
    ///     .expect("Failed to add FTL resources to the bundle.");
    ///
    /// // Register a fn that maps from string to string length
    /// bundle.add_function("STRLEN", |positional, _named| match positional {
    ///     [Some(FluentValue::String(str))] => Some(FluentValue::Number(str.len().to_string())),
    ///     _ => None,
    /// }).expect("Failed to add a function to the bundle.");
    ///
    /// let (value, _) = bundle.format("length", None)
    ///     .expect("Failed to format a message.");
    /// assert_eq!(&value, "5");
    /// ```
    ///
    /// [FTL syntax guide]: https://projectfluent.org/fluent/guide/functions.html
    pub fn add_function<F>(&mut self, id: &str, func: F) -> Result<(), FluentError>
    where
        F: 'bundle
            + Fn(&[Option<FluentValue>], &HashMap<&str, FluentValue>) -> Option<FluentValue>
            + Sync
            + Send,
    {
        match self.entries.entry(id.to_owned()) {
            HashEntry::Vacant(entry) => {
                entry.insert(Entry::Function(Box::new(func)));
                Ok(())
            }
            HashEntry::Occupied(_) => Err(FluentError::Overriding {
                kind: "function",
                id: id.to_owned(),
            }),
        }
    }

    /// Adds the message or messages, in [FTL syntax], to the bundle, returning an
    /// empty [`Result<T>`] on success.
    ///
    /// # Examples
    ///
    /// ```
    /// use fluent_bundle::{FluentBundle, FluentResource};
    ///
    /// let ftl_string = String::from("
    /// hello = Hi!
    /// goodbye = Bye!
    /// ");
    /// let resource = FluentResource::try_new(ftl_string)
    ///     .expect("Could not parse an FTL string.");
    /// let mut bundle = FluentBundle::new(&["en-US"]);
    /// bundle.add_resource(&resource)
    ///     .expect("Failed to add FTL resources to the bundle.");
    /// assert_eq!(true, bundle.has_message("hello"));
    /// ```
    ///
    /// # Whitespace
    ///
    /// Message ids must have no leading whitespace. Message values that span
    /// multiple lines must have leading whitespace on all but the first line. These
    /// are standard FTL syntax rules that may prove a bit troublesome in source
    /// code formatting. The [`indoc!`] crate can help with stripping extra indentation
    /// if you wish to indent your entire message.
    ///
    /// [FTL syntax]: https://projectfluent.org/fluent/guide/
    /// [`indoc!`]: https://github.com/dtolnay/indoc
    /// [`Result<T>`]: https://doc.rust-lang.org/std/result/enum.Result.html
    pub fn add_resource(&mut self, res: &'bundle FluentResource) -> Result<(), Vec<FluentError>> {
        let mut errors = vec![];

        for entry in &res.ast().body {
            let id = match entry {
                ast::ResourceEntry::Entry(ast::Entry::Message(ast::Message { ref id, .. }))
                | ast::ResourceEntry::Entry(ast::Entry::Term(ast::Term { ref id, .. })) => id.name,
                _ => continue,
            };

            let (entry, kind) = match entry {
                ast::ResourceEntry::Entry(ast::Entry::Message(message)) => {
                    (Entry::Message(message), "message")
                }
                ast::ResourceEntry::Entry(ast::Entry::Term(term)) => (Entry::Term(term), "term"),
                _ => continue,
            };

            match self.entries.entry(id.to_string()) {
                HashEntry::Vacant(empty) => {
                    empty.insert(entry);
                }
                HashEntry::Occupied(_) => {
                    errors.push(FluentError::Overriding {
                        kind,
                        id: id.to_string(),
                    });
                }
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// Formats the message value identified by `path` using `args` to
    /// provide variables. `path` is either a message id ("hello"), or
    /// message id plus attribute ("hello.tooltip").
    ///
    /// # Examples
    ///
    /// ```
    /// use fluent_bundle::{FluentBundle, FluentResource, FluentValue};
    /// use std::collections::HashMap;
    ///
    /// let ftl_string = String::from("intro = Welcome, { $name }.");
    /// let resource = FluentResource::try_new(ftl_string)
    ///     .expect("Could not parse an FTL string.");
    /// let mut bundle = FluentBundle::new(&["en-US"]);
    /// bundle.add_resource(&resource)
    ///     .expect("Failed to add FTL resources to the bundle.");
    ///
    /// let mut args = HashMap::new();
    /// args.insert("name", FluentValue::from("Rustacean"));
    ///
    /// let (value, _) = bundle.format("intro", Some(&args))
    ///     .expect("Failed to format a message.");
    /// assert_eq!(&value, "Welcome, Rustacean.");
    ///
    /// ```
    ///
    /// An example with attributes and no args:
    ///
    /// ```
    /// use fluent_bundle::{FluentBundle, FluentResource};
    ///
    /// let ftl_string = String::from("
    /// hello =
    ///     .title = Hi!
    ///     .tooltip = This says 'Hi!'
    /// ");
    /// let resource = FluentResource::try_new(ftl_string)
    ///     .expect("Could not parse an FTL string.");
    /// let mut bundle = FluentBundle::new(&["en-US"]);
    /// bundle.add_resource(&resource)
    ///     .expect("Failed to add FTL resources to the bundle.");
    ///
    /// let (value, _) = bundle.format("hello.title", None)
    ///     .expect("Failed to format a message.");
    /// assert_eq!(&value, "Hi!");
    /// ```
    ///
    /// # Errors
    ///
    /// For some cases where `format` can't find a message it will return `None`.
    ///
    /// In all other cases `format` returns a string even if it
    /// encountered errors. Generally, during partial errors `format` will
    /// use `'___'` to replace parts of the formatted message that it could
    /// not successfuly build. For more fundamental errors `format` will return
    /// the path itself as the translation.
    ///
    /// The second term of the tuple will contain any extra error information
    /// gathered during formatting. A caller may safely ignore the extra errors
    /// if the fallback formatting policies are acceptable.
    ///
    /// ```
    /// use fluent_bundle::{FluentBundle, FluentResource};
    ///
    /// // Create a message with bad cyclic reference
    /// let ftl_string = String::from("foo = a { foo } b");
    /// let resource = FluentResource::try_new(ftl_string)
    ///     .expect("Could not parse an FTL string.");
    /// let mut bundle = FluentBundle::new(&["en-US"]);
    /// bundle.add_resource(&resource)
    ///     .expect("Failed to add FTL resources to the bundle.");
    ///
    /// // The result falls back to "___"
    /// let (value, _) = bundle.format("foo", None)
    ///     .expect("Failed to format a message.");
    /// assert_eq!(&value, "___");
    /// ```
    pub fn format(
        &self,
        path: &str,
        args: Option<&HashMap<&str, FluentValue>>,
    ) -> Option<(String, Vec<FluentError>)> {
        let env = Env::new(self, args);

        let mut errors = vec![];

        if let Some(ptr_pos) = path.find('.') {
            let message_id = &path[..ptr_pos];
            let message = self.entries.get_message(message_id)?;
            let attr_name = &path[(ptr_pos + 1)..];
            for attribute in message.attributes.iter() {
                if attribute.id.name == attr_name {
                    match attribute.to_value(&env) {
                        Ok(val) => {
                            return Some((val.format(self), errors));
                        }
                        Err(err) => {
                            errors.push(FluentError::ResolverError(err));
                            // XXX: In the future we'll want to get the partial
                            // value out of resolver and return it here.
                            // We also expect to get a Vec or errors out of resolver.
                            return Some((path.to_string(), errors));
                        }
                    }
                }
            }
        } else {
            let message_id = path;
            let message = self.entries.get_message(message_id)?;
            match message.to_value(&env) {
                Ok(val) => {
                    let s = val.format(self);
                    return Some((s, errors));
                }
                Err(err) => {
                    errors.push(FluentError::ResolverError(err));
                    return Some((message_id.to_string(), errors));
                }
            }
        }

        None
    }

    /// Formats both the message value and attributes identified by `message_id`
    /// using `args` to provide variables. This is useful for cases where a UI
    /// element requires multiple related text fields, such as a button that has
    /// both display text and assistive text.
    ///
    /// # Examples
    ///
    /// ```
    /// use fluent_bundle::{FluentBundle, FluentResource, FluentValue};
    /// use std::collections::HashMap;
    ///
    /// let ftl_string = String::from("
    /// login-input = Predefined value
    ///     .placeholder = example@email.com
    ///     .aria-label = Login input value
    ///     .title = Type your login email
    /// ");
    /// let resource = FluentResource::try_new(ftl_string)
    ///     .expect("Could not parse an FTL string.");
    /// let mut bundle = FluentBundle::new(&["en-US"]);
    /// bundle.add_resource(&resource)
    ///     .expect("Failed to add FTL resources to the bundle.");
    ///
    /// let (message, _) = bundle.compound("login-input", None)
    ///     .expect("Failed to format a message.");
    /// assert_eq!(message.value, Some("Predefined value".to_string()));
    /// assert_eq!(message.attributes.get("title"), Some(&"Type your login email".to_string()));
    /// ```
    ///
    /// # Errors
    ///
    /// For some cases where `compound` can't find a message it will return `None`.
    ///
    /// In all other cases `compound` returns a message even if it
    /// encountered errors. Generally, during partial errors `compound` will
    /// use `'___'` to replace parts of the formatted message that it could
    /// not successfuly build. For more fundamental errors `compound` will return
    /// the path itself as the translation.
    ///
    /// The second term of the tuple will contain any extra error information
    /// gathered during formatting. A caller may safely ignore the extra errors
    /// if the fallback formatting policies are acceptable.
    pub fn compound(
        &self,
        message_id: &str,
        args: Option<&HashMap<&str, FluentValue>>,
    ) -> Option<(Message, Vec<FluentError>)> {
        let mut errors = vec![];

        let env = Env::new(self, args);
        let message = self.entries.get_message(message_id)?;

        let value = message
            .value
            .as_ref()
            .and_then(|value| match value.to_value(&env) {
                Ok(value) => Some(value.format(self)),
                Err(err) => {
                    errors.push(FluentError::ResolverError(err));
                    None
                }
            });

        let mut attributes = HashMap::new();

        for attr in message.attributes.iter() {
            match attr.to_value(&env) {
                Ok(value) => {
                    let val = value.format(self);
                    attributes.insert(attr.id.name.to_owned(), val);
                }
                Err(err) => {
                    errors.push(FluentError::ResolverError(err));
                }
            }
        }

        Some((Message { value, attributes }, errors))
    }
}


///
/// entry.rs
///
type FluentFunction<'bundle> = Box<
    'bundle
        + Fn(&[Option<FluentValue>], &HashMap<&str, FluentValue>) -> Option<FluentValue>
        + Send
        + Sync,
>;

pub enum Entry<'bundle> {
    Message(&'bundle ast::Message<'bundle>),
    Term(&'bundle ast::Term<'bundle>),
    Function(FluentFunction<'bundle>),
}

pub trait GetEntry<'bundle> {
    fn get_term(&self, id: &str) -> Option<&ast::Term>;
    fn get_message(&self, id: &str) -> Option<&ast::Message>;
    fn get_function(&self, id: &str) -> Option<&FluentFunction<'bundle>>;
}

impl<'bundle> GetEntry<'bundle> for HashMap<String, Entry<'bundle>> {
    fn get_term(&self, id: &str) -> Option<&ast::Term> {
        self.get(id).and_then(|entry| match *entry {
            Entry::Term(term) => Some(term),
            _ => None,
        })
    }

    fn get_message(&self, id: &str) -> Option<&ast::Message> {
        self.get(id).and_then(|entry| match *entry {
            Entry::Message(message) => Some(message),
            _ => None,
        })
    }

    fn get_function(&self, id: &str) -> Option<&FluentFunction<'bundle>> {
        self.get(id).and_then(|entry| match entry {
            Entry::Function(function) => Some(function),
            _ => None,
        })
    }
}


///
/// errors.rs
///
#[derive(Debug, Fail, PartialEq)]
pub enum FluentError {
    #[fail(display = "attempted to override an existing {}: {}", kind, id)]
    Overriding { kind: &'static str, id: String },
    #[fail(display = "Parser error")]
    ParserError(ParserError),
    #[fail(display = "Resolver error")]
    ResolverError(ResolverError),
}

impl From<ParserError> for FluentError {
    fn from(error: ParserError) -> Self {
        FluentError::ParserError(error)
    }
}

impl From<ResolverError> for FluentError {
    fn from(error: ResolverError) -> Self {
        FluentError::ResolverError(error)
    }
}


///
/// resolve.rs
///
#[derive(Debug, PartialEq)]
pub enum ResolverError {
    None,
    Value,
    Cyclic,
}

/// State for a single `ResolveValue::to_value` call.
pub struct Env<'env> {
    /// The current `FluentBundle` instance.
    pub bundle: &'env FluentBundle<'env>,
    /// The current arguments passed by the developer.
    pub args: Option<&'env HashMap<&'env str, FluentValue>>,
    /// Tracks hashes to prevent infinite recursion.
    pub travelled: RefCell<Vec<u64>>,
}

impl<'env> Env<'env> {
    pub fn new(
        bundle: &'env FluentBundle,
        args: Option<&'env HashMap<&'env str, FluentValue>>,
    ) -> Self {
        Env {
            bundle,
            args,
            travelled: RefCell::new(Vec::new()),
        }
    }

    fn track<F>(&self, identifier: &str, action: F) -> Result<FluentValue, ResolverError>
    where
        F: FnMut() -> Result<FluentValue, ResolverError>,
    {
        let mut hasher = DefaultHasher::new();
        identifier.hash(&mut hasher);
        let hash = hasher.finish();

        if self.travelled.borrow().contains(&hash) {
            Err(ResolverError::Cyclic)
        } else {
            self.travelled.borrow_mut().push(hash);
            self.scope(action)
        }
    }

    fn scope<T, F: FnMut() -> T>(&self, mut action: F) -> T {
        let level = self.travelled.borrow().len();
        let output = action();
        self.travelled.borrow_mut().truncate(level);
        output
    }
}

/// Converts an AST node to a `FluentValue`.
pub trait ResolveValue {
    fn to_value(&self, env: &Env) -> Result<FluentValue, ResolverError>;
}

impl<'source> ResolveValue for ast::Message<'source> {
    fn to_value(&self, env: &Env) -> Result<FluentValue, ResolverError> {
        env.track(&self.id.name, || {
            self.value
                .as_ref()
                .ok_or(ResolverError::None)?
                .to_value(env)
        })
    }
}

impl<'source> ResolveValue for ast::Term<'source> {
    fn to_value(&self, env: &Env) -> Result<FluentValue, ResolverError> {
        env.track(&self.id.name, || self.value.to_value(env))
    }
}

impl<'source> ResolveValue for ast::Attribute<'source> {
    fn to_value(&self, env: &Env) -> Result<FluentValue, ResolverError> {
        env.track(&self.id.name, || self.value.to_value(env))
    }
}

impl<'source> ResolveValue for ast::Pattern<'source> {
    fn to_value(&self, env: &Env) -> Result<FluentValue, ResolverError> {
        let mut string = String::with_capacity(128);
        for elem in &self.elements {
            let result: Result<String, ()> = env.scope(|| match elem.to_value(env) {
                Err(ResolverError::Cyclic) => Err(()),
                Err(_) => Ok("___".into()),
                Ok(elem) => Ok(elem.format(env.bundle)),
            });

            match result {
                Err(()) => return Ok("___".into()),
                Ok(value) => {
                    string.push_str(&value);
                }
            }
        }
        string.shrink_to_fit();
        Ok(FluentValue::from(string))
    }
}

impl<'source> ResolveValue for ast::PatternElement<'source> {
    fn to_value(&self, env: &Env) -> Result<FluentValue, ResolverError> {
        match self {
            ast::PatternElement::TextElement(s) => Ok(FluentValue::from(*s)),
            ast::PatternElement::Placeable(p) => p.to_value(env),
        }
    }
}

impl<'source> ResolveValue for ast::VariantKey<'source> {
    fn to_value(&self, _env: &Env) -> Result<FluentValue, ResolverError> {
        match self {
            ast::VariantKey::Identifier { name } => Ok(FluentValue::from(*name)),
            ast::VariantKey::NumberLiteral { value } => {
                FluentValue::into_number(value).map_err(|_| ResolverError::Value)
            }
        }
    }
}

impl<'source> ResolveValue for ast::Expression<'source> {
    fn to_value(&self, env: &Env) -> Result<FluentValue, ResolverError> {
        match self {
            ast::Expression::InlineExpression(exp) => exp.to_value(env),
            ast::Expression::SelectExpression { selector, variants } => {
                if let Ok(ref selector) = selector.to_value(env) {
                    for variant in variants {
                        match variant.key {
                            ast::VariantKey::Identifier { name } => {
                                let key = FluentValue::from(name);
                                if key.matches(env.bundle, selector) {
                                    return variant.value.to_value(env);
                                }
                            }
                            ast::VariantKey::NumberLiteral { value } => {
                                if let Ok(key) = FluentValue::into_number(value) {
                                    if key.matches(env.bundle, selector) {
                                        return variant.value.to_value(env);
                                    }
                                } else {
                                    return Err(ResolverError::Value);
                                }
                            }
                        }
                    }
                }

                select_default(variants)
                    .ok_or(ResolverError::None)?
                    .value
                    .to_value(env)
            }
        }
    }
}

impl<'source> ResolveValue for ast::InlineExpression<'source> {
    fn to_value(&self, env: &Env) -> Result<FluentValue, ResolverError> {
        match self {
            ast::InlineExpression::StringLiteral { value } => {
                Ok(FluentValue::from(unescape_unicode(value).into_owned()))
            }
            ast::InlineExpression::NumberLiteral { value } => {
                FluentValue::into_number(*value).map_err(|_| ResolverError::None)
            }
            ast::InlineExpression::FunctionReference { id, arguments } => {
                let (resolved_positional_args, resolved_named_args) = get_arguments(env, arguments);

                let func = env.bundle.entries.get_function(id.name);

                func.ok_or(ResolverError::None).and_then(|func| {
                    func(resolved_positional_args.as_slice(), &resolved_named_args)
                        .ok_or(ResolverError::None)
                })
            }
            ast::InlineExpression::MessageReference { id, attribute } => {
                let msg = env
                    .bundle
                    .entries
                    .get_message(&id.name)
                    .ok_or(ResolverError::None)?;
                if let Some(attribute) = attribute {
                    for attr in msg.attributes.iter() {
                        if attr.id.name == attribute.name {
                            return attr.to_value(env);
                        }
                    }
                    Err(ResolverError::None)
                } else {
                    msg.to_value(env)
                }
            }
            ast::InlineExpression::TermReference {
                id,
                attribute,
                arguments,
            } => {
                let term = env
                    .bundle
                    .entries
                    .get_term(&id.name)
                    .ok_or(ResolverError::None)?;

                let (.., resolved_named_args) = get_arguments(env, arguments);
                let env = Env::new(env.bundle, Some(&resolved_named_args));

                if let Some(attribute) = attribute {
                    for attr in term.attributes.iter() {
                        if attr.id.name == attribute.name {
                            return attr.to_value(&env);
                        }
                    }
                    Err(ResolverError::None)
                } else {
                    term.to_value(&env)
                }
            }
            ast::InlineExpression::VariableReference { id } => env
                .args
                .and_then(|args| args.get(&id.name))
                .cloned()
                .ok_or(ResolverError::None),
            ast::InlineExpression::Placeable { ref expression } => {
                let exp = expression.as_ref();
                exp.to_value(env)
            }
        }
    }
}

fn select_default<'source>(
    variants: &'source [ast::Variant<'source>],
) -> Option<&ast::Variant<'source>> {
    for variant in variants {
        if variant.default {
            return Some(variant);
        }
    }

    None
}

fn get_arguments<'env>(
    env: &Env,
    arguments: &'env Option<ast::CallArguments>,
) -> (Vec<Option<FluentValue>>, HashMap<&'env str, FluentValue>) {
    let mut resolved_positional_args = Vec::new();
    let mut resolved_named_args = HashMap::new();

    if let Some(ast::CallArguments { named, positional }) = arguments {
        for expression in positional {
            resolved_positional_args.push(expression.to_value(env).ok());
        }

        for arg in named {
            if let Ok(arg_value) = arg.value.to_value(env) {
                resolved_named_args.insert(arg.name.name, arg_value);
            }
        }
    }

    (resolved_positional_args, resolved_named_args)
}


///
/// resource.rs
///
rental! {
    mod rentals {
        use super::*;
        #[rental(covariant, debug)]
        pub struct FluentResource {
            string: String,
            ast: ast::Resource<'string>,
        }
    }
}

#[derive(Debug)]
pub struct FluentResource(rentals::FluentResource);

impl FluentResource {
    pub fn try_new(source: String) -> Result<Self, (Self, Vec<ParserError>)> {
        let mut errors = None;
        let res = rentals::FluentResource::new(source, |s| match parse(s) {
            Ok(ast) => ast,
            Err((ast, err)) => {
                errors = Some(err);
                ast
            }
        });

        if let Some(errors) = errors {
            return Err((Self(res), errors));
        } else {
            return Ok(Self(res));
        }
    }

    pub fn ast(&self) -> &ast::Resource {
        self.0.all().ast
    }
}


///
/// types.rs
///
/// Value types which can be formatted to a String.
#[derive(Clone, Debug, PartialEq)]
pub enum FluentValue {
    /// Fluent String type.
    String(String),
    /// Fluent Number type.
    Number(String),
}

impl FluentValue {
    pub fn into_number<S: ToString>(v: S) -> Result<Self, ParseFloatError> {
        f64::from_str(&v.to_string()).map(|_| FluentValue::Number(v.to_string()))
    }

    pub fn format(&self, _bundle: &FluentBundle) -> String {
        match self {
            FluentValue::String(s) => s.clone(),
            FluentValue::Number(n) => n.clone(),
        }
    }

    pub fn matches(&self, bundle: &FluentBundle, other: &FluentValue) -> bool {
        match (self, other) {
            (&FluentValue::String(ref a), &FluentValue::String(ref b)) => a == b,
            (&FluentValue::Number(ref a), &FluentValue::Number(ref b)) => a == b,
            (&FluentValue::String(ref a), &FluentValue::Number(ref b)) => {
                let cat = match a.as_str() {
                    "zero" => PluralCategory::ZERO,
                    "one" => PluralCategory::ONE,
                    "two" => PluralCategory::TWO,
                    "few" => PluralCategory::FEW,
                    "many" => PluralCategory::MANY,
                    "other" => PluralCategory::OTHER,
                    _ => return false,
                };

                let pr = &bundle.plural_rules;
                pr.select(b.as_str()) == Ok(cat)
            }
            (&FluentValue::Number(..), &FluentValue::String(..)) => false,
        }
    }
}

impl From<String> for FluentValue {
    fn from(s: String) -> Self {
        FluentValue::String(s)
    }
}

impl<'a> From<&'a str> for FluentValue {
    fn from(s: &'a str) -> Self {
        FluentValue::String(String::from(s))
    }
}

impl From<f32> for FluentValue {
    fn from(n: f32) -> Self {
        FluentValue::Number(n.to_string())
    }
}

impl From<isize> for FluentValue {
    fn from(n: isize) -> Self {
        FluentValue::Number(n.to_string())
    }
}


///
/// test interface
///
#[wasm_bindgen]
struct TestInterface {
    cache: HashMap<String, FluentBundle>
}

#[wasm_bindgen]
impl TestInterface {
    pub fn new() -> Self {
        TestInterface {
            cache: HashMap::new()
        }
    }

    pub fn create_bundle(
        &mut self,
        bundle_id: String,
        locales: String
    ) -> bool {
        let mut bundle = FluentBundle::new(&[locales]);
        self.cache.insert(bundle_id, bundle);
        return true;
    }

    pub fn has_message(
        &self,
        bundle_id: String,
        id: &str
    ) -> bool {
        let bundle = self.cache.get(&bundle_id).unwrap();
        return bundle.has_message(id);
    }

    pub fn add_function(
        &self,
        bundle_id: String,
        id: &str, func: F
    ) -> Result<(), FluentError>
    where
        F: 'bundle
            + Fn(&[Option<FluentValue>], &HashMap<&str, FluentValue>) -> Option<FluentValue>
            + Sync
            + Send,
    {
        let bundle = self.cache.get(&bundle_id).unwrap();
        return bundle.add_function(id, func);
    }

    pub fn add_resource(
        &self,
        bundle_id: String,
        res: &'bundle FluentResource
    ) -> Result<(), Vec<FluentError>> {
        let bundle = self.cache.get(&bundle_id).unwrap();
        return bundle.add_resource(res);
    }

    pub fn format(
        &self,
        bundle_id: String,
        path: &str,
        args: Option<&HashMap<&str, FluentValue>>
    ) -> Option<(String, Vec<FluentError>)> {
        let bundle = self.cache.get(&bundle_id).unwrap();
        return bundle.format(path, args);
    }

    pub fn compound(
        &self,
        bundle_id: String,
        message_id: &str,
        args: Option<&HashMap<&str, FluentValue>>
    ) -> Option<(Message, Vec<FluentError>)> {
        let bundle = self.cache.get(&bundle_id).unwrap();
        return bundle.compound(message_id, args);
    }
}
