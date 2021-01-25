use std::path::PathBuf;

support::slotmap_keyable! { Src }


#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SrcAttribution {
	pub id: SrcKey,
	pub range: Option<(u32, u32)>
}


#[derive(Debug)]
pub struct Src {
	pub content: String,
	pub path: PathBuf,
	pub lines: Vec<u32>,
}