use sha2::{Sha256, Digest};
use std::borrow::{Borrow, BorrowMut};
use std::cmp::min;
use std::rc::{Rc, Weak};
use std::cell::RefCell;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum TreeError {
    #[error("Invalid index")]
    IndexError,
    #[error("Inner hash error")]
    InnerHashZeroError,
    #[error("total is 1, inner_hashes must be zero")]
    TotalInnerHashMismatch,
    #[error("Expected inner hashes")]
    ExpectedInnerHash,
}

#[derive(Clone, Debug)]
pub struct ProofNode {
    pub hash: [u8; 32],
    pub parent: Option<Rc<RefCell<ProofNode>>>,
    pub left: Option<Rc<RefCell<ProofNode>>>,
    pub right: Option<Rc<RefCell<ProofNode>>>,
}

#[derive(Debug)]
pub struct Proof {
    pub total: i64,
    pub index: i64,
    pub leaf_hash: [u8; 32],
    pub aunts: Vec<[u8; 32]>,
}

pub const LEAF_PREFIX: &[u8] = &[0];
pub const INNER_PREFIX: &[u8] = &[1];

pub fn hash(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    let result: [u8; 32] = hasher.finalize().into();
    result
}

pub fn empty_hash() -> [u8; 32] {
    hash(&[])
}

pub fn leaf_hash(bytes: &[u8]) -> [u8; 32] {
    hash([LEAF_PREFIX, bytes].concat().as_slice())
}

pub fn inner_hash(left: &[u8], right: &[u8]) -> [u8; 32] {
    hash([INNER_PREFIX, left, right].concat().as_slice())
}

// rewrite this to arithetic-based computation
// make it easier for zk prover
fn get_split_point(length: u32) -> u32 {
    length.next_power_of_two() / 2
}

pub fn hash_from_byte_slices(items: &[&[u8]]) -> [u8; 32] {
    match items.len() {
        0 => empty_hash(),
        1 => leaf_hash(items[0]),
        _ => {
            let k: u32 = get_split_point(items.len() as u32);
            let left_hash = hash_from_byte_slices(&items[..k as usize]);
            let right_hash = hash_from_byte_slices(&items[k as usize..]);
            inner_hash(&left_hash, &right_hash)
        }
    }
}

pub fn trails_from_byte_slices(items: &[&[u8]]) -> (Vec<Rc<RefCell<ProofNode>>>, Rc<RefCell<ProofNode>>) {
    match items.len() {
        0 => (vec![], Rc::new(RefCell::new(ProofNode {
            hash: empty_hash(),
            parent: None,
            left: None,
            right: None,
        }))),
        1 => {
            let leaf_hash = leaf_hash(items[0]);
            let trail = Rc::new(RefCell::new(ProofNode {
                hash: leaf_hash,
                parent: None,
                left: None,
                right: None,
            }));
            (vec![trail.clone()], trail)
        }
        _ => {
            let k: u32 = get_split_point(items.len() as u32);
            let (lefts, mut left_root) = trails_from_byte_slices(&items[..k as usize]);
            let (rights, mut right_root) = trails_from_byte_slices(&items[k as usize..]);

            // compute the inner_hash of the left_root and right_roots
            let root_hash = inner_hash(&left_root.as_ref().borrow().hash, &right_root.as_ref().borrow().hash);
            let root_node = Rc::new(RefCell::new(ProofNode {
                hash: root_hash,
                parent: None,
                left: None,
                right: None,
            }));

            // update the parent of the left and right roots
            let mut l = left_root.as_ref().borrow_mut();
            l.parent = Some(root_node.clone());
            l.right = Some(right_root.clone());
            let mut r = right_root.as_ref().borrow_mut();
            r.parent = Some(root_node.clone());
            r.left = Some(left_root.clone());

            return (vec![lefts, rights].concat(), root_node)
        }
    }
}

pub fn proofs_from_byte_slices(items: &[&[u8]]) -> ([u8; 32], Vec<Proof>) {
    let (trails, root) = trails_from_byte_slices(items);
    let root_hash = root.as_ref().borrow().hash.clone();
    let proofs = trails.iter().enumerate().map(|(i, trail)| {
        let aunts = trail.as_ref().borrow().flatten_aunts();
        let leaf_hash = trail.as_ref().borrow().hash.clone();
        let total = items.len() as i64;
        let index = i;
        Proof {
            total,
            index: i as i64,
            leaf_hash,
            aunts,
        }
    }).collect();
    (root_hash, proofs)
}

pub fn compute_hash_from_aunts(index: i64, total: i64, leaf_hash: [u8; 32], inner_hashes: Vec<[u8; 32]>) -> Result<[u8; 32], TreeError> {
    if index > total || index < 0 || total <= 0 {
        return Err(TreeError::IndexError)
    }
    if total == 0 {
        return Err(TreeError::InnerHashZeroError)
    }
    if total == 1 {
        if inner_hashes.len() != 0 {
            return Err(TreeError::TotalInnerHashMismatch)
        }
        return Ok(leaf_hash)
    }
    if inner_hashes.len()  == 0 {
        return Err(TreeError::ExpectedInnerHash)
    }
    let num_left = get_split_point(total as u32) as i64;
    if index < num_left {
        let left_hash = compute_hash_from_aunts(index, num_left, leaf_hash, inner_hashes[..inner_hashes.len() - 1].to_vec())?;
        return Ok(inner_hash(&left_hash, &inner_hashes[inner_hashes.len() - 1]))
    }
    let right_hash = compute_hash_from_aunts(index - num_left, total - num_left, leaf_hash, inner_hashes[..inner_hashes.len() - 1].to_vec())?;
    return Ok(inner_hash(&inner_hashes[inner_hashes.len() - 1], &right_hash))
}

impl Proof {
    pub fn verify(&self, root_hash: [u8; 32]) -> bool {
        println!("len aunts: {:?}", self.aunts.len());
        let computed_hash = compute_hash_from_aunts(self.index, self.total, self.leaf_hash, self.aunts.clone()).unwrap();
        computed_hash == root_hash
    }
}

impl ProofNode {
    pub fn flatten_aunts(&self) -> Vec<[u8; 32]> {
        let mut inner_hashes: Vec<[u8; 32]> = vec![];
        let mut node: Option<Rc<RefCell<ProofNode>>> = Some(Rc::new(RefCell::new(self.clone())));
        while let Some(n) = node.take() {
            // if node has a left, add its hash to inner_hashes
            if let Some(left) = &n.as_ref().borrow().left {
                let left_hash = left.as_ref().borrow().hash.clone();
                inner_hashes.push(left_hash);
            }
            if let Some(right) = &n.as_ref().borrow().right {
                let right_hash = right.as_ref().borrow().hash.clone();
                inner_hashes.push(right_hash);
            }
            node = n.as_ref().borrow().parent.clone();
        }
        inner_hashes
    }
}