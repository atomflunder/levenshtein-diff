use std::cmp::{max, min};

use crate::util::*;

pub struct Levenshtein {
    pub weights: (usize, usize, usize),
}

impl Levenshtein {
    pub fn new(weights: (usize, usize, usize)) -> Self {
        Self { weights }
    }

    pub fn new_with_default_weights() -> Self {
        Self::new((1, 1, 1))
    }

    /// Returns the Levenshtein distance between source and target using Naive Recursion
    ///
    /// **It is ill-advised to use this function because of it's terrible performance
    /// characteristics.**
    ///
    /// This implementation has a time complexity of O(3^n).
    ///
    /// # Arguments
    ///
    /// * `source` - The source sequence
    /// * `target` - The target sequence
    ///
    /// # Examples
    ///
    /// ```
    /// use levenshtein_diff::Levenshtein;
    ///
    /// let s1 = "SATURDAY";
    /// let s2 = "SUNDAY";
    /// let expected_leven = 3;

    /// let lev = Levenshtein::new_with_default_weights();
    /// let lev_naive = lev.naive(s1.as_bytes(), s2.as_bytes());
    /// assert_eq!(lev_naive, expected_leven);
    /// ```
    pub fn naive<T: PartialEq>(&self, source: &[T], target: &[T]) -> usize {
        // base case
        if source.is_empty() || target.is_empty() {
            return max(source.len() * self.weights.1, target.len() * self.weights.0);
        }

        if source.last() == target.last() {
            // The item being looked at is the same, so it wouldn't contribute to the distance
            return self.naive(up_to_last(source), up_to_last(target));
        }

        let delete = self.naive(up_to_last(source), target) + self.weights.1;
        let insert = self.naive(source, up_to_last(target)) + self.weights.0;
        let substitute = self.naive(up_to_last(source), up_to_last(target)) + self.weights.2;

        min(min(insert, delete), substitute)
    }

    /// Returns the Levenshtein distance and the distance matrix between source and target using
    /// dynamic programming with tabulation.
    ///
    /// This implementation has a time complexity of O(n^2) and a space complexity of O(n^2).
    ///
    /// # Arguments
    ///
    /// * `source` - The source sequence
    /// * `target` - The target sequence
    ///
    /// # Examples
    ///
    /// ```
    /// use levenshtein_diff::Levenshtein;
    ///
    /// let s1 = "SATURDAY";
    /// let s2 = "SUNDAY";
    /// let expected_leven = 3;

    /// let lev = Levenshtein::new_with_default_weights();
    /// let (lev_tab, _) = lev.tabulation(s1.as_bytes(), s2.as_bytes());
    /// assert_eq!(lev_tab, expected_leven);
    /// ```
    pub fn tabulation<T: PartialEq>(&self, source: &[T], target: &[T]) -> (usize, DistanceMatrix) {
        let m = source.len();
        let n = target.len();

        // table of distances
        let mut distances = get_distance_table_with_weights(m, n, &self.weights);

        for i in 1..distances.table.len() {
            for j in 1..distances.table[0].len() {
                if source[i - 1] == target[j - 1] {
                    // The item being looked at is the same, so the distance won't increase
                    distances.table[i][j] = distances.table[i - 1][j - 1];
                    continue;
                }

                let delete = distances.table[i - 1][j] + self.weights.1;
                let insert = distances.table[i][j - 1] + self.weights.0;
                let substitute = distances.table[i - 1][j - 1] + self.weights.2;

                distances.table[i][j] = min(min(delete, insert), substitute);
            }
        }

        (distances.table[m][n], distances)
    }

    /// Returns the Levenshtein distance and the distance matrix between source and target using
    /// dynamic programming with memoization.
    ///
    /// This implementation has a time complexity of O(n^2) and a space complexity of O(n^2).
    ///
    /// # Arguments
    ///
    /// * `source` - The source sequence
    /// * `target` - The target sequence
    ///
    /// # Examples
    ///
    /// ```
    /// use levenshtein_diff::Levenshtein;
    ///
    /// let s1 = "SATURDAY";
    /// let s2 = "SUNDAY";
    /// let expected_leven = 3;

    /// let lev = Levenshtein::new_with_default_weights();
    /// let (lev_memo, _) = lev.memoization(s1.as_bytes(), s2.as_bytes());
    /// assert_eq!(lev_memo, expected_leven);
    /// ```
    pub fn memoization<T: PartialEq>(&self, source: &[T], target: &[T]) -> (usize, DistanceMatrix) {
        fn memoization_helper<T: PartialEq>(
            source: &[T],
            target: &[T],
            distances: &mut DistanceMatrix,
            weights: &(usize, usize, usize),
        ) -> usize {
            // check the cache first
            if distances.table[source.len()][target.len()] < usize::MAX {
                return distances.table[source.len()][target.len()];
            }

            // base case
            if source.is_empty() || target.is_empty() {
                return max(source.len(), target.len());
            }

            // couldn't find the value, time to recursively calculate it

            let k = if source.last() == target.last() {
                0
            } else {
                weights.2
            };

            let delete =
                memoization_helper(up_to_last(source), target, distances, weights) + weights.1;
            let insert =
                memoization_helper(source, up_to_last(target), distances, weights) + weights.0;
            let substitute =
                memoization_helper(up_to_last(source), up_to_last(target), distances, weights) + k;

            let distance = min(min(delete, insert), substitute);

            // update the cache
            distances.table[source.len()][target.len()] = distance;

            distance
        }

        let mut distances =
            get_distance_table_with_weights(source.len(), target.len(), &self.weights);

        let distance = memoization_helper(source, target, &mut distances, &self.weights);

        (distance, distances)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn levenshtein_naive_test() {
        let s1 = String::from("LAWN");
        let s2 = String::from("FFLAWANN");

        let lev = Levenshtein { weights: (1, 1, 1) };
        let lev_weight = Levenshtein { weights: (9, 5, 6) };

        assert_eq!(lev.naive(s1.as_bytes(), s2.as_bytes()), 4);
        assert_eq!(lev_weight.naive(s1.as_bytes(), s2.as_bytes()), 36);
    }

    #[test]
    fn levenshtein_memoization_test() {
        let s1 = String::from("LAWN");
        let s2 = String::from("FFLAWANN");

        let lev = Levenshtein { weights: (1, 1, 1) };
        let lev_weight = Levenshtein { weights: (9, 5, 6) };

        assert_eq!(lev.memoization(s1.as_bytes(), s2.as_bytes()).0, 4);
        assert_eq!(lev_weight.memoization(s1.as_bytes(), s2.as_bytes()).0, 36);
    }

    #[test]
    fn levenshtein_tabulation_test() {
        let s1 = String::from("LAWN");
        let s2 = String::from("FFLAWANN");

        let lev = Levenshtein { weights: (1, 1, 1) };
        let lev_weight = Levenshtein { weights: (9, 5, 6) };

        assert_eq!(lev.tabulation(s1.as_bytes(), s2.as_bytes()).0, 4);
        assert_eq!(lev_weight.tabulation(s1.as_bytes(), s2.as_bytes()).0, 36);
    }
}
