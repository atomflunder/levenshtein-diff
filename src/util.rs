pub type DistanceMatrix = Vec<Vec<usize>>;

pub fn print_table(table: &DistanceMatrix) {
    for row in table {
        for item in row {
            print!("{} ", item);
        }
        println!();
    }
}

pub fn get_distance_table(source_len: usize, target_len: usize) -> DistanceMatrix {
    get_distance_table_weights(source_len, target_len, &(1, 1, 1))
}

// Returns an initialized distance table of dimensions m+1 * n+1
// Where the first row is 0..n+1
// The First column is 0..m+1
// And the rest of the values are usize::MAX
pub fn get_distance_table_weights(
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

    distances
}

pub fn up_to_last<T>(slice: &[T]) -> &[T] {
    slice.split_last().map_or(&[], |(_, rest)| rest)
}
