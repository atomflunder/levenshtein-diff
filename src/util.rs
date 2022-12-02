/// Represents the edit distance matrix in a struct holding the table and the given weights for Insertion, Deletion and Substitution.
pub struct DistanceMatrix {
    pub table: Vec<Vec<usize>>,
    pub weights: (usize, usize, usize),
}

impl DistanceMatrix {
    /// Creates a new DistanceMatrix struct with the given table and weights.
    pub fn new(matrix: Vec<Vec<usize>>, weights: (usize, usize, usize)) -> Self {
        Self {
            table: matrix,
            weights,
        }
    }

    /// Creates a new DistanceMatrix struct with the given table and default weights all set to 1.
    pub fn new_with_default_weights(matrix: Vec<Vec<usize>>) -> Self {
        Self::new(matrix, (1, 1, 1))
    }

    /// Prints the distance matrix table in a human readable format.
    pub fn print_table(&self) {
        for row in &self.table {
            for item in row {
                print!("{} ", item);
            }
            println!();
        }
    }
}

// Returns an initialized distance table of dimensions m+1 * n+1
// Where the first row is 0..n+1
// The First column is 0..m+1
// And the rest of the values are usize::MAX
pub fn get_distance_table(m: usize, n: usize) -> DistanceMatrix {
    let weights = (1, 1, 1);
    let mut distances = Vec::with_capacity(m + 1);

    // The first row
    distances.push((0..n + 1).into_iter().map(|x| x * weights.1).collect());

    for i in 1..m + 1 {
        // initialize the whole row to sentinel
        distances.push(vec![usize::MAX; n + 1]);
        // update the first item in the row
        distances[i][0] = i * weights.0;
    }

    DistanceMatrix::new(distances, weights)
}

pub fn get_distance_table_with_weights(
    m: usize,
    n: usize,
    weights: &(usize, usize, usize),
) -> DistanceMatrix {
    let mut distances = Vec::with_capacity(m + 1);

    // The first row
    distances.push((0..n + 1).into_iter().map(|x| x * weights.0).collect());

    for i in 1..m + 1 {
        // initialize the whole row to sentinel
        distances.push(vec![usize::MAX; n + 1]);
        // update the first item in the row
        distances[i][0] = i * weights.0;
    }

    DistanceMatrix::new(distances, *weights)
}

pub fn up_to_last<T>(slice: &[T]) -> &[T] {
    slice.split_last().map_or(&[], |(_, rest)| rest)
}
