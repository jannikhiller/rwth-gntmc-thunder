use std::ops::Index;

#[derive(PartialEq, Debug)]
pub struct SparseMatrix<ValueType> {
    values: Vec<ValueType>,
    col_indexes: Vec<usize>,
    row_offsets: Vec<usize>,
    cols: usize,
    default_value: ValueType,
}

#[derive(PartialEq, Debug)]
pub struct SparseMatrixElement<'a, ValueType> {
    pub col_index: usize,
    pub value: &'a ValueType,
}

pub struct SparseMatrixRowIter<'a, ValueType> {
    matrix: &'a SparseMatrix<ValueType>,
    pos: usize,
    row_end: usize,
}

pub struct SparseMatrixIter<'a, ValueType> {
    matrix: &'a SparseMatrix<ValueType>,
    row_index: usize,
}

impl<'a, ValueType> IntoIterator for &'a SparseMatrix<ValueType> {
    type Item = SparseMatrixRowIter<'a, ValueType>;
    type IntoIter = SparseMatrixIter<'a, ValueType>;

    fn into_iter(self) -> Self::IntoIter {
        SparseMatrixIter {
            matrix: self,
            row_index: 0,
        }
    }
}

impl<'a, ValueType> Iterator for SparseMatrixIter<'a, ValueType> {
    type Item = SparseMatrixRowIter<'a, ValueType>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.row_index >= self.matrix.rows() {
            return None;
        }
        let row_start = self.matrix.row_offsets[self.row_index];
        let row_end = self.matrix.row_offsets[self.row_index + 1];
        let row_iter = SparseMatrixRowIter {
            matrix: self.matrix,
            pos: row_start,
            row_end,
        };
        self.row_index += 1;
        Some(row_iter)
    }
}

impl<'a, ValueType> Iterator for SparseMatrixRowIter<'a, ValueType> {
    type Item = SparseMatrixElement<'a, ValueType>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos >= self.row_end {
            return None;
        }
        let item = SparseMatrixElement {
            value: &self.matrix.values[self.pos],
            col_index: self.matrix.col_indexes[self.pos],
        };
        self.pos += 1;
        Some(item)
    }
}

impl<ValueType: Default + PartialEq + Copy> SparseMatrix<ValueType> {
    pub fn new() -> Self {
        SparseMatrix {
            values: Vec::new(),
            col_indexes: Vec::new(),
            row_offsets: vec![0],
            cols: 0,
            default_value: ValueType::default(),
        }
    }

    pub fn from_2d_vec(input_vec: &[Vec<ValueType>]) -> Self {
        let rows = input_vec.len();
        if rows == 0 {
            return SparseMatrix::new();
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
                if *value == default_value {
                    continue;
                }
                values.push(*value);
                col_indexes.push(col_index);
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

    pub fn from_list_of_entries(
        num_rows: usize,
        num_cols: usize,
        entries: &[(usize, usize, ValueType)],
    ) -> Self {
        let mut sorted_entries = entries.to_vec();
        sorted_entries.sort_by_key(|&(r, c, _)| (r, c));
        SparseMatrix::from_sorted_list_of_entries(num_rows, num_cols, &sorted_entries)
    }

    pub fn from_sorted_list_of_entries(
        num_rows: usize,
        num_cols: usize,
        entries: &[(usize, usize, ValueType)],
    ) -> Self {
        let mut values = Vec::with_capacity(entries.len());
        let mut col_indexes = Vec::with_capacity(entries.len());
        let mut row_offsets = vec![0; num_rows + 1];
        let default_value = ValueType::default();

        for chunk in entries.chunk_by(|&(r0, _, _), &(r1, _, _)| r0 == r1) {
            for &(row_index, col_index, value) in chunk {
                if row_index >= num_rows || col_index >= num_cols {
                    panic!(
                        "Element at {:?} is outside the dimensions of the matrix.",
                        (row_index, col_index)
                    );
                }
                if col_indexes.len() > row_offsets[row_index]
                    && *col_indexes.last().unwrap() == col_index
                {
                    panic!("Found multiple elements with the same coordinates.");
                }
                if value == default_value {
                    continue;
                }
                values.push(value);
                col_indexes.push(col_index);
                row_offsets[row_index + 1] += 1;
            }
        }

        // now row_offsets only contains the length of each row. If we do a cummulative sum on it,
        // we get the correct offsets:
        row_offsets.iter_mut().fold(0, |acc, offset| {
            *offset += acc;
            *offset
        });

        SparseMatrix {
            values,
            col_indexes,
            row_offsets,
            cols: num_cols,
            default_value,
        }
    }
}

impl<ValueType> SparseMatrix<ValueType> {
    pub fn rows(&self) -> usize {
        return self.row_offsets.len() - 1;
    }
    pub fn cols(&self) -> usize {
        return self.cols;
    }
    pub fn get(&self, row_index: usize, col_index: usize) -> Result<&ValueType, &str> {
        if row_index >= self.rows() || col_index >= self.cols() {
            return Err("Index out of bounds");
        }
        let row_start = self.row_offsets[row_index];
        let row_end = self.row_offsets[row_index + 1];
        let maybe_index = self.col_indexes[row_start..row_end].binary_search(&col_index);
        match maybe_index {
            Ok(i) => Ok(&self.values[row_start + i]),
            Err(_) => Ok(&self.default_value),
        }
    }
    pub fn get_col_indexes_in_row(&self, row_index: usize) -> &[usize] {
        if row_index >= self.rows() {
            panic!("Index out of bounds");
        }
        &self.col_indexes[self.row_offsets[row_index]..self.row_offsets[row_index + 1]]
    }

    pub fn get_row(&self, row_index: usize) -> SparseMatrixRowIter<ValueType> {
        if row_index >= self.rows() {
            panic!("Index out of bounds");
        }
        let row_start = self.row_offsets[row_index];
        let row_end = self.row_offsets[row_index + 1];
        SparseMatrixRowIter {
            matrix: self,
            pos: row_start,
            row_end,
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

// tests partially written by chatgpt
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

        let input_vec: Vec<Vec<u32>> = vec![vec![], vec![]];
        let m = SparseMatrix::from_2d_vec(&input_vec);
        assert_eq!(m.values, vec![]);
        assert_eq!(m.col_indexes, vec![]);
        assert_eq!(m.row_offsets, vec![0, 0, 0]);
        assert_eq!(m.cols, 0);
    }

    #[test]
    fn test_from_list_of_entries() {
        let entries = vec![(1, 1, 30), (0, 0, 10), (2, 2, 50), (2, 0, 40), (0, 2, 20)];
        let matrix = SparseMatrix::from_list_of_entries(3, 3, &entries);

        assert_eq!(matrix.values, vec![10, 20, 30, 40, 50]);
        assert_eq!(matrix.col_indexes, vec![0, 2, 1, 0, 2]);
        assert_eq!(matrix.row_offsets, vec![0, 2, 3, 5]);
        assert_eq!(matrix.cols, 3);
        assert_eq!(matrix.default_value, 0);

        // double index:
        let entries = vec![(0, 1, 30), (0, 0, 10), (0, 1, 10)];
        let result = std::panic::catch_unwind(|| {
            SparseMatrix::from_list_of_entries(2, 2, &entries);
        });
        assert!(result.is_err());

        // out of bounds:
        let entries = vec![(0, 1, 30), (0, 0, 10), (0, 30, 10)];
        let result = std::panic::catch_unwind(|| {
            SparseMatrix::from_list_of_entries(2, 2, &entries);
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
    #[test]
    fn test_get_col_indexes_in_row() {
        let matrix = SparseMatrix {
            values: vec![10, 20, 30],
            col_indexes: vec![0, 2, 1],
            row_offsets: vec![0, 2, 3],
            cols: 4,
            default_value: 0,
        };

        assert_eq!(matrix.get_col_indexes_in_row(0), &[0, 2]); // Should return column indexes [0, 2]
        assert_eq!(matrix.get_col_indexes_in_row(1), &[1]); // Should return column indexes [1]
        let result = std::panic::catch_unwind(|| {
            matrix.get_col_indexes_in_row(2); // This should panic because row index 2 is out of bounds
        });
        assert!(result.is_err());
    }

    #[test]
    fn test_get_row() {
        /*
         * 10  0 20  0
         *  0 30  0  0
         */
        let matrix = SparseMatrix {
            values: vec![10, 20, 30],
            col_indexes: vec![0, 2, 1],
            row_offsets: vec![0, 2, 3],
            cols: 4,
            default_value: 0,
        };
        let first_row: Vec<SparseMatrixElement<'_, i32>> = matrix.get_row(0).collect();
        assert_eq!(first_row.len(), 2); // Should have 2 items
        assert_eq!(
            first_row[0],
            SparseMatrixElement {
                value: &10,
                col_index: 0
            }
        ); // First item in row
        assert_eq!(
            first_row[1],
            SparseMatrixElement {
                value: &20,
                col_index: 2
            }
        ); // Second item in row

        let second_row: Vec<SparseMatrixElement<'_, i32>> = matrix.get_row(1).collect();
        assert_eq!(second_row.len(), 1); // Should have 1 item
        assert_eq!(
            second_row[0],
            SparseMatrixElement {
                value: &30,
                col_index: 1
            }
        ); // Only item in row

        let result = std::panic::catch_unwind(|| {
            matrix.get_row(2).for_each(|_| {}); // This should panic because row index 2 is out of bounds
        });
        assert!(result.is_err());
    }

    #[test]
    fn test_sparse_matrix_iter() {
        let matrix = SparseMatrix {
            values: vec![10, 20, 30],
            col_indexes: vec![0, 2, 1],
            row_offsets: vec![0, 2, 3],
            cols: 4,
            default_value: 0,
        };

        let mut iter = matrix.into_iter();

        // Collect the first row
        let first_row: Vec<SparseMatrixElement<'_, i32>> = iter.next().unwrap().collect();
        assert_eq!(first_row.len(), 2); // Should have 2 items
        assert_eq!(
            first_row[0],
            SparseMatrixElement {
                value: &10,
                col_index: 0
            }
        ); // First item in row
        assert_eq!(
            first_row[1],
            SparseMatrixElement {
                value: &20,
                col_index: 2
            }
        ); // Second item in row

        // Collect the second row
        let second_row: Vec<SparseMatrixElement<'_, i32>> = iter.next().unwrap().collect();
        assert_eq!(second_row.len(), 1); // Should have 1 item
        assert_eq!(
            second_row[0],
            SparseMatrixElement {
                value: &30,
                col_index: 1
            }
        ); // Only item in row

        // Test that there are no more rows
        assert!(iter.next().is_none());
    }
}
