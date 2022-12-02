pub mod distance;
pub mod edit;
pub mod util;

pub use distance::*;
pub use edit::*;
use util::DistanceMatrix;

/// Computes and returns the Levenshtein distance between the source and target sequences.
///
/// # Arguments
///
/// * `source` - The source sequence
/// * `target` - The target sequence
///
/// # Examples
///
/// ```
/// use levenshtein_diff as levenshtein;
///
/// let s1 = "FLAW";
/// let s2 = "LAWN";
///
/// let (distance, _) = levenshtein::distance(s1.as_bytes(), s2.as_bytes());
/// assert_eq!(distance, 2);
///
/// let v1 = vec![0, 1, 2];
/// let v2 = vec![1, 2, 3, 4];
///
/// let (distance, _) = levenshtein::distance(&v1[..], &v2[..]); // Also works on vectors
/// assert_eq!(distance, 3);
/// ```
pub fn distance<T: PartialEq>(source: &[T], target: &[T]) -> (usize, DistanceMatrix) {
    let lev = Levenshtein { weights: (1, 1, 1) };
    lev.memoization(source, target)
}

/// Computes and returns the Levenshtein distance between the source and target sequences
/// with the specified weights for Insertion, Deletion and Substitution.
///
/// # Arguments
///
/// * `source` - The source sequence
/// * `target` - The target sequence
/// * `weights` - The weights for Insertion, Deletion and Substitution
///
/// # Examples
///
/// ```
/// use levenshtein_diff as levenshtein;
///
/// let s1 = "FLAW";
/// let s2 = "LAWN";
/// let weights = (1, 1, 2);
///
/// let (distance, _) = levenshtein::distance_with_weights(s1.as_bytes(), s2.as_bytes(), weights);
/// assert_eq!(distance, 2);
///
/// let v1 = vec![0, 1, 2];
/// let v2 = vec![1, 2, 3, 4];
/// let weights = (2, 2, 2);
///
/// let (distance, _) = levenshtein::distance_with_weights(&v1[..], &v2[..], weights); // Also works on vectors
/// assert_eq!(distance, 6);
/// ```
pub fn distance_with_weights<T: PartialEq>(
    source: &[T],
    target: &[T],
    weights: (usize, usize, usize),
) -> (usize, DistanceMatrix) {
    let lev = Levenshtein { weights };
    lev.memoization(source, target)
}

#[cfg(test)]
mod tests {
    use crate::*;
    #[test]
    fn default_distance_test() {
        let s1 = "FLOWER";
        let s2 = "FOLLOWER";

        let expected_dist = 2;

        let (dist, _) = distance(s1.as_bytes(), s2.as_bytes());

        assert_eq!(expected_dist, dist);
    }
}
