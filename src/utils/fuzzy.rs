/// Fuzzy matching utilities for "did you mean?" suggestions
///
/// This module provides Levenshtein distance-based fuzzy matching to suggest
/// similar names when encountering undefined variables, properties, or modules.
use std::cmp::min;

/// Calculate Levenshtein distance between two strings
///
/// Returns the minimum number of single-character edits (insertions, deletions, substitutions)
/// required to transform one string into another.
///
/// Time complexity: O(n * m) where n and m are the lengths of the strings
/// Space complexity: O(min(n, m)) due to optimizations
pub fn levenshtein_distance(a: &str, b: &str) -> usize {
    let a_lower = a.to_lowercase();
    let b_lower = b.to_lowercase();

    let a_chars: Vec<char> = a_lower.chars().collect();
    let b_chars: Vec<char> = b_lower.chars().collect();

    let a_len = a_chars.len();
    let b_len = b_chars.len();

    // Early exit optimizations
    if a_len == 0 {
        return b_len;
    }
    if b_len == 0 {
        return a_len;
    }

    // Use a single row for space optimization (instead of full matrix)
    let mut prev_row: Vec<usize> = (0..=b_len).collect();
    let mut curr_row: Vec<usize> = vec![0; b_len + 1];

    for i in 1..=a_len {
        curr_row[0] = i;

        for j in 1..=b_len {
            let cost = if a_chars[i - 1] == b_chars[j - 1] {
                0
            } else {
                1
            };

            curr_row[j] = min(
                min(
                    curr_row[j - 1] + 1, // insertion
                    prev_row[j] + 1,     // deletion
                ),
                prev_row[j - 1] + cost, // substitution
            );
        }

        std::mem::swap(&mut prev_row, &mut curr_row);
    }

    prev_row[b_len]
}

/// Find similar names from a list of candidates
///
/// Returns candidates that are within the specified maximum edit distance,
/// sorted by similarity (closest match first).
///
/// # Arguments
/// * `target` - The target string to match against
/// * `candidates` - List of candidate strings
/// * `max_distance` - Maximum edit distance to consider (inclusive)
///
/// # Returns
/// Vector of (candidate, distance) pairs, sorted by distance (ascending)
pub fn find_similar_names(
    target: &str,
    candidates: &[String],
    max_distance: usize,
) -> Vec<(String, usize)> {
    let mut matches: Vec<(String, usize)> = Vec::new();

    // Early exit for exact match
    for candidate in candidates {
        if candidate.eq_ignore_ascii_case(target) {
            return vec![(candidate.clone(), 0)];
        }
    }

    // Length filter: skip candidates with length difference > max_distance
    let target_len = target.len();
    let filtered_candidates: Vec<&String> = candidates
        .iter()
        .filter(|c| {
            let len_diff = if c.len() > target_len {
                c.len() - target_len
            } else {
                target_len - c.len()
            };
            len_diff <= max_distance
        })
        .take(100) // Limit to 100 candidates for performance
        .collect();

    for candidate in filtered_candidates {
        let distance = levenshtein_distance(target, candidate);

        if distance <= max_distance {
            matches.push((candidate.clone(), distance));
        }
    }

    // Sort by distance (closest first)
    matches.sort_by_key(|(_, dist)| *dist);

    matches
}

/// Suggest the best similar name from candidates
///
/// Returns the single best match if one exists within a reasonable threshold.
/// The threshold is calculated as: max(3, target.len() / 3)
///
/// # Arguments
/// * `target` - The target string to match against
/// * `candidates` - List of candidate strings
///
/// # Returns
/// The best matching candidate, or None if no good match exists
pub fn suggest_similar(target: &str, candidates: &[String]) -> Option<String> {
    // Calculate adaptive threshold
    let threshold = std::cmp::max(3, target.len() / 3);

    let matches = find_similar_names(target, candidates, threshold);

    // Return the best match (if any)
    matches.first().map(|(name, _)| name.clone())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_exact_match() {
        assert_eq!(levenshtein_distance("hello", "hello"), 0);
        assert_eq!(levenshtein_distance("", ""), 0);
    }

    #[test]
    fn test_one_char_difference() {
        assert_eq!(levenshtein_distance("hello", "hallo"), 1); // substitution
        assert_eq!(levenshtein_distance("hello", "hell"), 1); // deletion
        assert_eq!(levenshtein_distance("hello", "helloo"), 1); // insertion
    }

    #[test]
    fn test_case_insensitive() {
        assert_eq!(levenshtein_distance("Hello", "hello"), 0);
        assert_eq!(levenshtein_distance("WORLD", "world"), 0);
    }

    #[test]
    fn test_empty_strings() {
        assert_eq!(levenshtein_distance("", "hello"), 5);
        assert_eq!(levenshtein_distance("hello", ""), 5);
    }

    #[test]
    fn test_completely_different() {
        assert_eq!(levenshtein_distance("abc", "xyz"), 3);
    }

    #[test]
    fn test_find_similar_names_exact_match() {
        let candidates = vec![
            "userName".to_string(),
            "userEmail".to_string(),
            "userId".to_string(),
        ];

        let matches = find_similar_names("userName", &candidates, 3);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].0, "userName");
        assert_eq!(matches[0].1, 0);
    }

    #[test]
    fn test_find_similar_names_one_char_typo() {
        let candidates = vec![
            "userName".to_string(),
            "userEmail".to_string(),
            "userId".to_string(),
        ];

        let matches = find_similar_names("userNme", &candidates, 3);
        assert!(!matches.is_empty());
        assert_eq!(matches[0].0, "userName");
        assert_eq!(matches[0].1, 1);
    }

    #[test]
    fn test_find_similar_names_case_mismatch() {
        let candidates = vec!["username".to_string(), "userId".to_string()];

        let matches = find_similar_names("userName", &candidates, 3);
        assert!(!matches.is_empty());
        assert_eq!(matches[0].0, "username");
        assert_eq!(matches[0].1, 0); // Case insensitive
    }

    #[test]
    fn test_find_similar_names_no_match() {
        let candidates = vec!["foo".to_string(), "bar".to_string()];

        let matches = find_similar_names("verylongname", &candidates, 3);
        assert!(matches.is_empty());
    }

    #[test]
    fn test_suggest_similar_best_match() {
        let candidates = vec![
            "userName".to_string(),
            "userEmail".to_string(),
            "userId".to_string(),
        ];

        let suggestion = suggest_similar("userNme", &candidates);
        assert_eq!(suggestion, Some("userName".to_string()));
    }

    #[test]
    fn test_suggest_similar_no_match() {
        let candidates = vec!["foo".to_string(), "bar".to_string()];

        let suggestion = suggest_similar("completelydifferent", &candidates);
        assert_eq!(suggestion, None);
    }

    #[test]
    fn test_suggest_similar_exact_match() {
        let candidates = vec!["userName".to_string(), "userEmail".to_string()];

        let suggestion = suggest_similar("userName", &candidates);
        assert_eq!(suggestion, Some("userName".to_string()));
    }

    #[test]
    fn test_adaptive_threshold() {
        // Short string: threshold = 3
        let candidates = vec!["abc".to_string()];
        let suggestion = suggest_similar("xyz", &candidates);
        assert_eq!(suggestion, Some("abc".to_string())); // distance = 3, within threshold

        // Long string: threshold = len / 3 = 6
        let candidates = vec!["verylongname".to_string()];
        let suggestion = suggest_similar("verylogname", &candidates); // distance = 1
        assert_eq!(suggestion, Some("verylongname".to_string()));
    }
}
