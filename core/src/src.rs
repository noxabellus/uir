use std::{cmp::Ordering, path::PathBuf};

support::slotmap_keyable! { Src }


#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SrcAttribution {
	pub key: SrcKey,
	pub range: Option<(u32, u32)>
}


#[derive(Debug)]
pub struct Src {
	pub path: PathBuf,
	pub content: String,
	pub lines: Vec<u32>,
}

impl Src {
	pub fn new (path: PathBuf, content: String) -> Self {
		let mut lines = vec![0];

    let mut iter = content.char_indices();
    if let Some((_, mut last_ch)) = iter.next() {
      for (i, ch) in iter {
        if last_ch == '\n' { lines.push(i as u32); }
        last_ch = ch;
      }
    }

		Self {
			path,
			content,
			lines
		}
	}

	pub fn get_line_and_idx (&self, pos: u32) -> (u32, u32) {
    fn bin_search (slice: &[u32], value: &u32) -> usize {
      fn search (slice: &[u32], l: usize, r: usize, x: &u32) -> usize {
        if r > l {
          let mid = l + (r - l) / 2;

          match slice[mid].cmp(x) {
            Ordering::Equal => mid,
            Ordering::Greater => search(slice, l, mid - 1, x),
            Ordering::Less => search(slice, mid + 1, r, x)
          }
        } else {
          r
        }
      };

      search(slice, 0, slice.len() - 1, value)
    }

    let line = bin_search(&self.lines, &pos);

    (line as u32, self.lines[line])
  }

	pub fn get_line_col (&self, pos: u32) -> (u32, u32) {
    let (line, line_start) = self.get_line_and_idx(pos);
    let column = pos - line_start;

    (line, column)
  }
}