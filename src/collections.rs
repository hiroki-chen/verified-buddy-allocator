use vstd::{
    prelude::*,
    raw_ptr::{self, Dealloc, IsExposed},
};

verus! {

#[repr(C, align(8))]
pub struct PPtrWrapper<V>(vstd::simple_pptr::PPtr<V>);

pub tracked struct PointsToWrapper<V> {
    /// The underlying raw pointer permission.
    points_to: raw_ptr::PointsTo<V>,
    exposed: IsExposed,
    dealloc: Option<Dealloc>,
}

#[verifier::reject_recursive_types(V)]
#[verifier::ext_equal]
pub struct Node<V> {
    /// The previous node in the linked list.
    pub prev: Option<PPtrWrapper<Node<V>>>,
    /// The next node in the linked list.
    pub next: Option<PPtrWrapper<Node<V>>>,
    pub value: V,
}

#[verifier::reject_recursive_types(V)]
#[verifier::ext_equal]
pub tracked struct LinkedListInner<V> {
    pub ptrs: Seq<PPtrWrapper<Node<V>>>,
    pub perms: Map<nat, PointsToWrapper<Node<V>>>,
}

#[verifier::reject_recursive_types(V)]
#[verifier::ext_equal]
pub struct LinkedList<V> {
    pub head: Option<PPtrWrapper<Node<V>>>,
    pub tail: Option<PPtrWrapper<Node<V>>>,
    pub inner: Tracked<LinkedListInner<V>>,
    pub len: usize,
}

}
