use crate::common::sparse_matrix::SparseMatrix;

pub fn public() {
    let m = SparseMatrix::from_2d_vec(&vec![
        vec![2, 3, 0],
        vec![0, 1, 0],
        vec![0, 0, 0],
        vec![100, 0, 0],
    ]);

    println!("Printing elements of a sparse matrix:");
    for (i, row) in m.into_iter().enumerate() {
        print!("row {i}:");
        for elem in row {
            print!(" {elem:?}");
        }
        println!();
    }
}
