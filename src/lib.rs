pub(crate) use egg::*;

mod sketch;

pub use {
    sketch::Sketch
};

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn sketch_parse_and_print() {
        let string = "(contains (f ?))";
        let sketch = string.parse::<Sketch<SymbolLang>>().unwrap();
        assert_eq!(sketch.to_string(), string);
    }
}
