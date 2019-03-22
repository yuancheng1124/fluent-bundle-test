use std::collections::HashMap;
use wasm_bindgen::prelude::*;

struct FluentBundle {}

impl FluentBundle {
    pub fn new() -> Self {
        FluentBundle {}
    }
    
    pub fn format(&self, id: String) -> String {
        format!("This is a value for a key {}", id)
    }
}

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
    
    pub fn create_bundle(&mut self, bundle_id: String) -> bool {
        let bundle = FluentBundle::new();
        self.cache.insert(bundle_id, bundle);
        return true;
    }
    
    pub fn format(&self, bundle_id: String, id: String) -> String {
        let bundle = self.cache.get(&bundle_id).unwrap();
        return bundle.format(id);
    }
}

fn main() {
    let mut test = TestInterface::new();
    
    let bundle_id = String::from("test_bundle");
    test.create_bundle(bundle_id.clone());
    let value = test.format(bundle_id.clone(), String::from("key0"));
    assert_eq!(value, "This is a value for a key key0")
}
