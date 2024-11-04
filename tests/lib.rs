use core::ops::*;
use core::str::*;

use structured_map::*;

use MyStructKey::*;

// This structured map is added here to be used in tests and it is a test in on
// itself - it tests that the generated code compiles and that it can be used.
structured_map!(
    /// An example doc comment on the type itself.
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub(crate) MyStruct => [
        /// Some example comment.
        key1,
        /// Another key [`u32`].
        key2,
        /// A final key.
        key3
    ]
);

#[test]
fn key_enum_variant_string_representation_is_in_original_casing() {
    // Arrange
    let key = Key1;

    // Act
    let string = key.to_string();

    // Assert
    assert_eq!(string, "key1");
}

#[test]
fn key_enum_from_str_works_for_original_casing() {
    // Arrange
    let string = "key1";

    // Act
    let key = MyStructKey::from_str(string).unwrap();

    // Assert
    assert_eq!(key, Key1);
}

#[test]
fn key_enum_respects_roundtrip_property_for_from_str_and_display() {
    // Arrange
    let key = Key1;

    // Act
    let reconstructed_key =
        MyStructKey::from_str(key.to_string().as_str()).unwrap();

    // Assert
    assert_eq!(key, reconstructed_key);
}

#[test]
fn key_enum_pascal_case_string_fails_parsing() {
    // Arrange
    let string = "Key1";

    // Act
    let result = MyStructKey::from_str(string);

    // Assert
    assert!(result.is_err())
}

#[test]
fn key_enum_next_implementation_produces_the_correct_next_key() {
    // Arrange
    let expectations = [(Key1, Some(Key2)), (Key2, Some(Key3)), (Key3, None)];

    for (key, expected_next_key) in expectations {
        // Act
        let next_key = key.next();

        // Assert
        assert_eq!(next_key, expected_next_key)
    }
}

#[test]
fn key_enum_option_next_implementation_produces_the_correct_next_key() {
    // Arrange
    let expectations = [
        (None, Some(Key1)),
        (Some(Key1), Some(Key2)),
        (Some(Key2), Some(Key3)),
        (Some(Key3), None),
    ];

    for (key, expected_next_key) in expectations {
        // Act
        let next_key = MyStructKey::next_on_option(key.as_ref());

        // Assert
        assert_eq!(next_key, expected_next_key)
    }
}

#[test]
fn key_enum_iterator_type_iterates_in_expected_way() {
    // Arrange
    let mut iterator = MyStructKeyIterator::default();

    // Act
    let should_be_key1 = iterator.next();
    let should_be_key2 = iterator.next();
    let should_be_key3 = iterator.next();
    let should_be_none_first = iterator.next();
    let should_be_none_second = iterator.next();

    // Assert
    assert_eq!(should_be_key1, Some(Key1));
    assert_eq!(should_be_key2, Some(Key2));
    assert_eq!(should_be_key3, Some(Key3));
    assert_eq!(should_be_none_first, None);
    assert_eq!(should_be_none_second, None);
}

#[test]
fn structured_map_can_be_indexed_using_a_key() {
    // Arrange
    let mut structure = MyStruct {
        key1: 0,
        key2: 0,
        key3: 0,
    };

    // Act
    *IndexMut::index_mut(&mut structure, Key3) = 10;
    let key3 = structure[Key3];

    // Assert
    assert_eq!(key3, 10);
}

#[test]
fn structured_map_into_iter_iterates_in_expected_way() {
    // Arrange
    let structure = MyStruct {
        key1: 1,
        key2: 2,
        key3: 3,
    };
    let mut iterator = structure.into_iter();

    // Act
    let should_be1 = iterator.next();
    let should_be2 = iterator.next();
    let should_be3 = iterator.next();
    let should_be_none_first = iterator.next();
    let should_be_none_second = iterator.next();

    // Assert
    assert_eq!(should_be1, Some(1));
    assert_eq!(should_be2, Some(2));
    assert_eq!(should_be3, Some(3));
    assert_eq!(should_be_none_first, None);
    assert_eq!(should_be_none_second, None);
}

#[test]
fn structured_map_iter_iterates_in_expected_way() {
    // Arrange
    let structure = MyStruct {
        key1: 1,
        key2: 2,
        key3: 3,
    };
    let mut iterator = structure.iter();

    // Act
    let should_be1 = iterator.next();
    let should_be2 = iterator.next();
    let should_be3 = iterator.next();
    let should_be_none_first = iterator.next();
    let should_be_none_second = iterator.next();

    // Assert
    assert_eq!(should_be1, Some(&1));
    assert_eq!(should_be2, Some(&2));
    assert_eq!(should_be3, Some(&3));
    assert_eq!(should_be_none_first, None);
    assert_eq!(should_be_none_second, None);
}

#[test]
fn structured_map_can_be_instantiated_through_new_function() {
    // Arrange
    let expected_structure = MyStruct {
        key1: 1,
        key2: 2,
        key3: 3,
    };

    // Act
    let structure = MyStruct::new(1, 2, 3);

    // Assert
    assert_eq!(structure, expected_structure);
}

#[test]
fn structured_map_can_be_instantiated_through_from_fn_function() {
    // Arrange
    let expected_structure = MyStruct {
        key1: 1,
        key2: 2,
        key3: 3,
    };

    // Act
    let structure = MyStruct::from_fn(|key| match key {
        Key1 => 1,
        Key2 => 2,
        Key3 => 3,
    });

    // Assert
    assert_eq!(structure, expected_structure);
}

#[test]
fn structured_map_can_be_instantiated_through_try_from_fn_function() {
    // Arrange
    let expected_structure = MyStruct {
        key1: 1,
        key2: 2,
        key3: 3,
    };

    // Act
    let structure = MyStruct::try_from_fn(|key| match key {
        Key1 => Result::<_, std::convert::Infallible>::Ok(1),
        Key2 => Result::<_, std::convert::Infallible>::Ok(2),
        Key3 => Result::<_, std::convert::Infallible>::Ok(3),
    });

    // Assert
    assert_eq!(structure.unwrap(), expected_structure);
}

#[test]
fn structured_map_instantiation_fails_in_from_fn_if_err_is_returned() {
    // Act
    let structure = MyStruct::try_from_fn(|_| Result::<(), ()>::Err(()));

    // Assert
    assert!(structure.is_err())
}

#[test]
fn structured_map_map_performs_expected_conversion() {
    // Arrange
    let structure = MyStruct::from_fn(|_| 1);
    let expected_structure = MyStruct::from_fn(|_| "1".to_owned());

    // Act
    let mapped_structure = structure.map(|item| item.to_string());

    // Assert
    assert_eq!(mapped_structure, expected_structure)
}

#[test]
fn structured_map_try_map_performs_expected_conversion() {
    // Arrange
    let structure = MyStruct::from_fn(|_| 1);
    let expected_structure = MyStruct::from_fn(|_| "1".to_owned());

    // Act
    let mapped_structure =
        structure.try_map(|item| Result::<_, ()>::Ok(item.to_string()));

    // Assert
    assert_eq!(mapped_structure.unwrap(), expected_structure)
}

#[test]
fn structured_map_zip_performs_expected_operation() {
    // Arrange
    let numbers = MyStruct {
        key1: 1,
        key2: 2,
        key3: 3,
    };
    let number_chars = MyStruct {
        key1: '1',
        key2: '2',
        key3: '3',
    };
    let expected_structure = MyStruct {
        key1: (1, '1'),
        key2: (2, '2'),
        key3: (3, '3'),
    };

    // Act
    let zipped_structure = numbers.zip(number_chars);

    // Assert
    assert_eq!(zipped_structure, expected_structure)
}

#[test]
fn structured_map_as_ref_returns_a_structured_map_over_references() {
    // Arrange
    let structure = MyStruct {
        key1: 1,
        key2: 2,
        key3: 3,
    };
    let expected_structure = MyStruct {
        key1: &1,
        key2: &2,
        key3: &3,
    };

    // Act
    let as_ref_structure = structure.as_ref();

    // Assert
    assert_eq!(as_ref_structure, expected_structure)
}

#[test]
fn structured_map_as_mut_returns_a_structured_map_over_references() {
    // Arrange
    let mut structure = MyStruct {
        key1: 1,
        key2: 2,
        key3: 3,
    };
    let expected_structure = MyStruct {
        key1: &mut 1,
        key2: &mut 2,
        key3: &mut 3,
    };

    // Act
    let as_ref_structure = structure.as_mut();

    // Assert
    assert_eq!(as_ref_structure, expected_structure)
}
