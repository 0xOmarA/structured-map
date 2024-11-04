use structured_map::*;

#[test]
fn structured_map_compiles() {
    structured_map!(
        pub(crate) MyStruct => [
            /// Some example comment.
            key1,
            /// Another key [`u32`].
            key2,
            /// A final key.
            key3
        ]
    );
}
