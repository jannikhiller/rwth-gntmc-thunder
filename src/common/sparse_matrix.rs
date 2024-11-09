use std::ops::Index;

#[derive(PartialEq, Debug)]
pub struct SparseMatrix<ValueType> {
    values: Vec<ValueType>,
    col_indexes: Vec<usize>,
    row_offsets: Vec<usize>,
    cols: usize,
    default_value: ValueType,
}

impl<ValueType: Default> Default for SparseMatrix<ValueType> {
    fn default() -> Self {
        SparseMatrix {
            values: Vec::new(),
            col_indexes: Vec::new(),
            row_offsets: vec![0],
            cols: 0,
            default_value: ValueType::default(),
        }
    }
}

impl<ValueType: Default + PartialEq + Copy> SparseMatrix<ValueType> {
    fn from_2d_vec(input_vec: &[Vec<ValueType>]) -> Self {
        let rows = input_vec.len();
        if rows == 0 {
            return SparseMatrix::default();
        }
        let cols = input_vec[0].len();

        let mut values = Vec::new();
        let mut col_indexes = Vec::new();
        let mut row_offsets = vec![0];
        let default_value = ValueType::default();

        for row in input_vec {
            if row.len() != cols {
                panic!("Inconsistent number of columns");
            }
            for (col_index, value) in row.iter().enumerate() {
                if *value != default_value {
                    values.push(*value);
                    col_indexes.push(col_index);
                }
            }
            row_offsets.push(values.len());
        }
        SparseMatrix {
            values,
            col_indexes,
            row_offsets,
            cols,
            default_value,
        }
    }
}

impl<ValueType> SparseMatrix<ValueType> {
    fn rows(&self) -> usize {
        return self.row_offsets.len() - 1;
    }
    fn cols(&self) -> usize {
        return self.cols;
    }
    pub fn get(&self, row: usize, col: usize) -> Result<&ValueType, &str> {
        if row >= self.rows() || col >= self.cols() {
            return Err("Index out of bounds");
        }
        let row_start = self.row_offsets[row];
        let row_end = self.row_offsets[row + 1];
        let maybe_index = self.col_indexes[row_start..row_end].binary_search(&col);
        match maybe_index {
            Ok(i) => Ok(&self.values[row_start + i]),
            Err(_) => Ok(&self.default_value),
        }
    }
}

impl<ValueType> Index<(usize, usize)> for SparseMatrix<ValueType> {
    type Output = ValueType;
    fn index(&self, index: (usize, usize)) -> &Self::Output {
        match self.get(index.0, index.1) {
            Ok(value) => value,
            Err(_) => panic!("Index out of bounds"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sparse_matrix_get() {
        let matrix = SparseMatrix {
            values: vec![10, 20],
            col_indexes: vec![0, 2],
            row_offsets: vec![0, 2, 2],
            cols: 4,
            default_value: 0,
        };
        assert_eq!(*matrix.get(0, 0).unwrap(), 10); // Value at (0, 0) should be `10`
        assert_eq!(*matrix.get(0, 2).unwrap(), 20); // Value at (0, 2) should be `20`
        assert_eq!(*matrix.get(0, 1).unwrap(), 0); // Value at (0, 1) should be `0` (default)
        assert_eq!(*matrix.get(1, 1).unwrap(), 0); // Value at (1, 1) should be `0` (default)
        assert!(matrix.get(3, 0).is_err()); // Row index `3` is out of bounds
        assert!(matrix.get(0, 5).is_err()); // Column index `5` is out of bounds
    }

    #[test]
    fn test_sparse_matrix_from_2d_vec() {
        let input_vec = vec![vec![0, 1, 3], vec![0, 0, 0], vec![-1, 100, 1]];
        let m = SparseMatrix::from_2d_vec(&input_vec);
        assert_eq!(m.values, vec![1, 3, -1, 100, 1]);
        assert_eq!(m.col_indexes, vec![1, 2, 0, 1, 2]);
        assert_eq!(m.row_offsets, vec![0, 2, 2, 5]);
        assert_eq!(m.cols, 3);
        assert_eq!(m.default_value, 0);
        assert_eq!(m[(0, 0)], 0);
        assert_eq!(m[(2, 1)], 100);
        let result = std::panic::catch_unwind(|| {
            SparseMatrix::from_2d_vec(&vec![vec![1, 2, 3], vec![1]]);
        });
        assert!(result.is_err());
    }

    #[test]
    fn test_sparse_matrix_index() {
        let matrix = SparseMatrix {
            values: vec![10, 20],
            col_indexes: vec![0, 2],
            row_offsets: vec![0, 2, 2],
            cols: 4,
            default_value: 0,
        };

        assert_eq!(matrix[(0, 0)], 10); // Value at (0, 0) should be `10`
        assert_eq!(matrix[(0, 2)], 20); // Value at (0, 2) should be `20`
        assert_eq!(matrix[(0, 1)], 0); // Value at (0, 1) should be `0` (default)
        assert_eq!(matrix[(1, 1)], 0); // Value at (1, 1) should be `0` (default)
        let result = std::panic::catch_unwind(|| {
            matrix[(3, 0)] // This should panic because row index `3` is out of bounds
        });
        assert!(result.is_err());
        let result = std::panic::catch_unwind(|| {
            matrix[(0, 5)] // This should panic because column index `5` is out of bounds
        });
        assert!(result.is_err());
    }
}
