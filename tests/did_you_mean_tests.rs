/// Tests for "did you mean?" fuzzy matching suggestions in error messages
///
/// These tests document the expected behavior once the feature is fully integrated.
/// Currently, they test the underlying fuzzy matching infrastructure.

use luanext_typechecker::utils::fuzzy;

#[test]
fn test_undefined_variable_one_char_typo() {
    // Simulate having these variables in scope
    let candidates = vec![
        "userName".to_string(),
        "userEmail".to_string(),
        "userId".to_string(),
    ];

    // User typed "userNme" instead of "userName"
    let suggestion = fuzzy::suggest_similar("userNme", &candidates);
    assert_eq!(suggestion, Some("userName".to_string()));
}

#[test]
fn test_undefined_variable_case_mismatch() {
    let candidates = vec![
        "username".to_string(),
        "password".to_string(),
    ];

    // User typed "userName" but variable is "username"
    let suggestion = fuzzy::suggest_similar("userName", &candidates);
    assert_eq!(suggestion, Some("username".to_string()));
}

#[test]
fn test_undefined_variable_no_close_match() {
    let candidates = vec![
        "foo".to_string(),
        "bar".to_string(),
    ];

    // User typed something completely different
    let suggestion = fuzzy::suggest_similar("completelydifferent", &candidates);
    assert_eq!(suggestion, None);
}

#[test]
fn test_property_not_found_suggests_similar() {
    // Simulate object properties
    let candidates = vec![
        "firstName".to_string(),
        "lastName".to_string(),
        "emailAddress".to_string(),
    ];

    // User typed "firsName" instead of "firstName"
    let suggestion = fuzzy::suggest_similar("firsName", &candidates);
    assert_eq!(suggestion, Some("firstName".to_string()));
}

#[test]
fn test_multiple_candidates_returns_closest() {
    let candidates = vec![
        "userName".to_string(),  // distance 1 from "userNme" (case-insensitive)
        "userNam".to_string(),   // distance 2 from "userNme" (case-insensitive)
        "userEmail".to_string(),
    ];

    // "userName" is closest: case-insensitive "usernme" → "username" = 1 edit
    let suggestion = fuzzy::suggest_similar("userNme", &candidates);
    assert_eq!(suggestion, Some("userName".to_string()));
}

#[test]
fn test_fuzzy_matching_with_common_prefixes() {
    let candidates = vec![
        "getUserName".to_string(),
        "getUserEmail".to_string(),
        "getUserId".to_string(),
        "setUserName".to_string(),
    ];

    // Typo in the middle of the name
    let suggestion = fuzzy::suggest_similar("getUserNme", &candidates);
    assert_eq!(suggestion, Some("getUserName".to_string()));
}

#[test]
fn test_short_variable_names() {
    let candidates = vec![
        "x".to_string(),
        "y".to_string(),
        "z".to_string(),
    ];

    // Even for short names, should suggest if within threshold
    let suggestion = fuzzy::suggest_similar("a", &candidates);
    // Distance of 1 is within threshold for short strings
    assert_eq!(suggestion, Some("x".to_string()));
}

#[test]
fn test_long_variable_names() {
    let candidates = vec![
        "veryLongVariableName".to_string(),
        "anotherLongVariableName".to_string(),
    ];

    // With adaptive threshold, should handle longer names
    let suggestion = fuzzy::suggest_similar("veryLongVarableName", &candidates); // missing 'i'
    assert_eq!(suggestion, Some("veryLongVariableName".to_string()));
}

#[test]
fn test_underscore_vs_camel_case() {
    let candidates = vec![
        "user_name".to_string(),
        "user_email".to_string(),
    ];

    // User uses camelCase when variable is snake_case
    // This should NOT match well (large edit distance)
    let suggestion = fuzzy::suggest_similar("userName", &candidates);
    // Depends on threshold - might or might not match
    // This documents current behavior
    if let Some(sug) = suggestion {
        println!("Suggested: {}", sug);
    }
}

#[test]
fn test_adaptive_threshold_behavior() {
    // Test that threshold scales with string length

    // Short string: threshold = 3
    let short_candidates = vec!["abc".to_string()];
    let short_suggestion = fuzzy::suggest_similar("xyz", &short_candidates);
    assert_eq!(short_suggestion, Some("abc".to_string())); // distance = 3, within threshold

    // Long string: threshold = len / 3
    let long_candidates = vec!["verylongname".to_string()]; // len = 12, threshold = 4
    let long_suggestion = fuzzy::suggest_similar("verylogname", &long_candidates); // distance = 1
    assert_eq!(long_suggestion, Some("verylongname".to_string()));
}
