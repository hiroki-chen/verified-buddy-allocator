use vstd::{
    prelude::*,
    raw_ptr::{self, Dealloc, IsExposed},
};

verus! {

/// A fixed-size array wrapper over Rust's raw array type `[T; N]`.
#[repr(C)]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct Array<T, const N: usize>(pub [T; N]);

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

impl<T, const N: usize> Array<T, N> {
    pub uninterp spec fn idx(&self, i: int) -> T;

    /// Constructs a new [`Array`] from a raw array.
    ///
    /// This is marked as external_body because the inner type is opaque.
    #[verifier::external_body]
    pub const fn new(value: [T; N]) -> (s: Self) {
        Self(value)
    }

    pub const fn len(&self) -> usize
        returns
            N,
    {
        N
    }

    #[verifier::external_body]
    pub fn update_in_place<U>(&mut self, i: usize, f: impl FnOnce(T) -> (U, T)) -> (t: U)
        requires
            0 <= i < old(self)@.len(),
            old(self).wf(),
            old(self)@.index(i as int).wf(),
            f.requires((old(self)@.index(i as int),)),
        ensures
            self.wf(),
            f.ensures((old(self)@.index(i as int),), (t, self@.index(i as int))),
            self@.len() == old(self)@.len(),
            self@.index(i as int).wf(),
            // others remain unchanged.
            forall|j: int|
                0 <= j < old(self)@.len() as int && j != i as int ==> self@.index(j) == old(
                    self,
                )@.index(j),
    {
        let bad = unsafe { core::mem::MaybeUninit::<T>::uninit().assume_init() };
        let v = core::mem::replace(&mut self.0[i], bad);
        let (t, v) = f(v);
        self.0[i] = v;

        t
    }
}

impl<T, const N: usize> View for Array<T, N> {
    type V = Seq<T>;

    closed spec fn view(&self) -> Self::V {
        Seq::new(N as nat, |i| self.idx(i))
    }
}

impl<T: Clone, const N: usize> Clone for Array<T, N> {
    #[verifier::external_body]
    fn clone(&self) -> (r: Self)
        ensures
            r.wf(),
            r@ == self@,
    {
        Array(self.0.clone())
    }
}

impl<T: Copy, const N: usize> Copy for Array<T, N> {

}

impl<V> LinkedList<V> {
    pub open spec fn prev(&self, i: nat) -> Option<PPtrWrapper<Node<V>>> {
        if i == 0 {
            None
        } else {
            Some(self.inner@.ptrs[i as int - 1])
        }
    }

    pub open spec fn node_wf_at(&self, i: nat) -> bool {
        &&& self.inner@.perms[i].wf()
        &&& self.inner@.perms.dom().contains(i)
        &&& self.inner@.ptrs[i as int]@ == self.inner@.perms[i].pptr()
        &&& self.inner@.perms[i].mem_contents() matches vstd::simple_pptr::MemContents::Init(node)
            && node.prev == self.prev(i) && node.next == self.next(i)
    }

    pub open spec fn node_wf(&self) -> bool {
        forall|i: nat| 0 <= i < self.inner@.ptrs.len() ==> #[trigger] self.node_wf_at(i)
    }

    pub open spec fn next(&self, i: nat) -> Option<PPtrWrapper<Node<V>>> {
        if i == self.inner@.ptrs.len() as nat - 1 {
            None
        } else {
            Some(self.inner@.ptrs[i as int + 1])
        }
    }

    pub open spec fn is_empty(&self) -> bool {
        &&& self.head.is_none()
        &&& self.tail.is_none()
        &&& self.inner@.ptrs.len() == 0
    }

    pub open spec fn spec_len(&self) -> nat {
        self.inner@.ptrs.len() as nat
    }

    pub proof fn spec_len_is_len(&self)
        requires
            self.wf(),
        ensures
            self.spec_len() == self@.len(),
    {
    }

    pub proof fn is_empty_implies_len_zero(&self)
        requires
            self.wf(),
        ensures
            self.is_empty() <==> self.spec_len() == 0,
    {
    }

    pub const fn new() -> (s: Self)
        ensures
            s.wf(),
    {
        Self {
            head: None,
            tail: None,
            inner: Tracked(
                LinkedListInner { ptrs: Seq::tracked_empty(), perms: Map::tracked_empty() },
            ),
            len: 0,
        }
    }

    #[inline(always)]
    pub fn len(&self) -> (len: usize)
        requires
            self.wf(),
        ensures
            len == self@.len(),
    {
        self.len
    }

    fn push_empty(&mut self, v: PPtrWrapper<Node<V>>, perm: Tracked<PointsToWrapper<Node<V>>>)
        requires
            old(self).wf(),
            old(self)@.len() == 0,
            perm@.is_init(),
            perm@.wf(),
            perm@.value().value.wf(),
            perm@.value().prev == None::<PPtrWrapper<Node<V>>>,
            perm@.value().next == None::<PPtrWrapper<Node<V>>>,
            v@ == perm@.pptr(),
        ensures
            self.wf(),
            self@ =~= old(self)@.push(perm@.value().value),
            self.inner@.ptrs == old(self).inner@.ptrs.push(v),
    {
        self.tail = Some(v);
        self.head = Some(v);
        let Tracked(perm) = perm;
        self.len = self.len + 1;

        // Update ghost states.
        proof {
            self.inner.borrow_mut().ptrs.tracked_push(v);
            self.inner.borrow_mut().perms.tracked_insert((self.inner@.ptrs.len() - 1) as _, perm);
        }
    }

    /// Pushes to the front of the linked list without allocating any memory.
    pub fn push_front_no_alloc(
        &mut self,
        v: PPtrWrapper<Node<V>>,
        perm: Tracked<PointsToWrapper<Node<V>>>,
    )
        requires
            old(self).wf(),
            perm@.wf(),
            old(self).len < usize::MAX,
            perm@.value().value.wf(),
            v@ == perm@.pptr(),
            perm@.is_init(),
        ensures
            self.wf(),
            self@ == seq![perm@.value().value].add(old(self)@),
            self.inner@.ptrs == seq![v].add(old(self).inner@.ptrs),
    {
        let Tracked(mut points_to) = perm;
        let val = v.take(Tracked(&mut points_to));
        match self.head {
            None => {
                v.write(Tracked(&mut points_to), Node { prev: None, next: None, value: val.value });

                self.push_empty(v, Tracked(points_to));
            },
            Some(old_head_ptr) => {
                proof {
                    assert(self.inner@.ptrs.len() > 0);
                    assert(self.node_wf_at(0));
                }
                self.len = self.len + 1;

                // Now we update the node pointers.
                v.write(
                    Tracked(&mut points_to),
                    Node { prev: None, next: Some(old_head_ptr), value: val.value },
                );

                assert(self.inner@.perms.dom().contains(0));
                let tracked mut old_head_points_to = self.inner.borrow_mut().perms.tracked_remove(
                    0,
                );
                assert(!self.inner@.perms.dom().contains(0));
                let mut old_head_node = old_head_ptr.take(Tracked(&mut old_head_points_to));
                old_head_node.prev = Some(v);
                old_head_ptr.write(Tracked(&mut old_head_points_to), old_head_node);
                proof {
                    // Update the ghost states.
                    self.inner.borrow_mut().perms.tracked_insert(0, old_head_points_to);
                }
                self.head = Some(v);

                // Simultaneously, we update the ghost states.
                proof {
                    assert forall|i: nat|
                        0 <= i < old(
                            self,
                        ).inner@.ptrs.len() implies self.inner@.perms.dom().contains(i) by {
                        assert(old(self).node_wf_at(i));
                    }

                    // Update keys.
                    self.inner.borrow_mut().perms.tracked_map_keys_in_place(
                        Map::<nat, nat>::new(
                            |i: nat| 1 <= i <= old(self)@.len() as nat,
                            |i: nat| (i - 1) as nat,
                        ),  // self.index(j) == old(self).index(key_map.index(j))
                    );

                    self.inner.borrow_mut().ptrs.tracked_insert(0, v);
                    self.inner.borrow_mut().perms.tracked_insert(0, points_to);

                    assert(self@ =~= seq![perm@.value().value].add(old(self)@));
                    assert(self.node_wf_at(0));
                    // Some additional proofs on wellformed.
                    assert(forall|i: nat|
                        1 <= i <= old(self).inner@.ptrs.len() && old(self).node_wf_at(
                            (i - 1) as nat,
                        ) ==> #[trigger] self.node_wf_at(i));
                    assert forall|i: int|
                        1 <= i <= self.inner@.ptrs.len() as int - 1 implies #[trigger] old(
                        self,
                    ).inner@.ptrs.index(i - 1) == self.inner@.ptrs.index(i) by {
                        assert(old(self).node_wf_at((i - 1) as nat));
                    }

                    assert(self.node_wf_at(1));
                }
            },
        }
    }

    /// Pops the first element of the linked list.
    ///
    /// This API is marked `no_alloc` because it does not allocate any memory, and thus it
    /// requires the caller to manage the raw pointer; de-allocating it when it is no longer needed.
    pub fn pop_front_no_alloc(&mut self) -> (res: (
        PPtrWrapper<Node<V>>,
        Tracked<PointsToWrapper<Node<V>>>,
    ))
        requires
            old(self).wf(),
            !old(self).is_empty(),
        ensures
            res.0 == old(self).inner@.ptrs.index(0),
            res.1@.value().value == old(self)@.index(0),
            self@ == old(self)@.remove(0),
            self.inner@.ptrs == old(self).inner@.ptrs.remove(0),
            self.wf(),
    {
        proof {
            // Unfold that definition so we indeed know that the head node is well formed.
            // so we can remove it from the permission map.
            assert(self.node_wf_at(0));
        }

        self.len = self.len - 1;
        let head = self.head.unwrap();
        let tracked head_points_to = self.inner.borrow_mut().perms.tracked_remove(0);
        let v = head.borrow(Tracked(&mut head_points_to));

        match v.next {
            None => {
                self.head = None;
                self.tail = None;

                proof {
                    assert(self.inner@.ptrs.len() == 1);
                }
            },
            Some(next) => {
                assert(old(self)@.len() > 1);
                assert(old(self).node_wf_at(1));  // for dom().contains(1).

                self.head = Some(next);
                let tracked mut next_points_to = self.inner.borrow_mut().perms.tracked_remove(1);

                // Modify the next node so that its prev becomes None and it should be the head node.
                let mut next_node = next.take(Tracked(&mut next_points_to));
                next_node.prev = None;
                next.write(Tracked(&mut next_points_to), next_node);

                // Now we update the ghost states.
                proof {
                    // We update the points to map.
                    self.inner.borrow_mut().perms.tracked_insert(1, next_points_to);

                    // Now update the permission map by shifting the keys.
                    assert forall|i: nat|
                        1 <= i < old(self)@.len() implies self.inner@.perms.dom().contains(i) by {
                        assert(old(self).node_wf_at(i));
                    }

                    // Update keys. => self.index(j) == old(self).index(key_map.index(i + 1)) by left.
                    self.inner.borrow_mut().perms.tracked_map_keys_in_place(
                        Map::<nat, nat>::new(
                            |i: nat| 0 <= i && i < old(self)@.len() - 1,
                            |i: nat| (i + 1) as nat,
                        ),
                    );
                }
            },
        }

        // Update pointers.
        proof {
            // let this = self.inner.borrow_mut().ptrs.tracked_remove(0);
            // self.inner.borrow_mut().ptrs = (self)@.remove(0);
            self.inner.borrow_mut().ptrs.tracked_pop_front();

            if self.inner@.ptrs.len() > 0 {
                assert(self.node_wf_at(0));
                assert(forall|i: nat|
                    0 < i < self@.len() && old(self).node_wf_at(i + 1)
                        ==> #[trigger] self.node_wf_at(i));

                assert forall|i: int| 0 <= i && i < self@.len() implies #[trigger] self@[i] == old(
                    self,
                )@.subrange(1, old(self)@.len() as int)[i] by {
                    assert(old(self).node_wf_at(i as nat + 1));
                };
                assert(self@ =~= old(self)@.remove(0));
                assert(self.tail == Some(self.inner@.ptrs[self.inner@.ptrs.len() as int - 1]));
                assert(self.head == Some(self.inner@.ptrs[0]));
            } else {
                assert(self.wf());
            }
        }

        (head, Tracked(head_points_to))
    }

    /// Removes the element at the given index from the linked list.
    ///
    /// This is the slowest part of a primitive buddy allocator, because it runs in
    /// O(log N) time where N is the number of blocks of a given size.
    pub fn remove(&mut self, i: usize) -> (ret: (
        PPtrWrapper<Node<V>>,
        Tracked<PointsToWrapper<Node<V>>>,
    ))
        requires
            old(self).wf(),
            0 <= i < old(self).inner@.ptrs.len(),
            !old(self).is_empty(),
        ensures
            ret.0 == old(self).inner@.ptrs.index(i as int),
            ret.1@.value().value == old(self)@.index(i as int),
            self@ =~= old(self)@.remove(i as int),
            self.inner@.ptrs == old(self).inner@.ptrs.remove(i as int),
            self.wf(),
    {
        // If we are removing the first element, we can use the pop_front_no_alloc method.
        if i == 0 {
            return self.pop_front_no_alloc();
        }
        let mut idx = 0;
        let mut ptr = self.head;

        while idx < i - 1
            invariant
                idx < i < self.inner@.ptrs.len(),
                forall|j: nat| 0 <= j < self.inner@.ptrs.len() ==> #[trigger] self.node_wf_at(j),
                ptr matches Some(p) && p == self.inner@.ptrs[idx as int],
            decreases i - idx,
        {
            proof {
                assert(self.node_wf_at(idx as nat));
            }
            // Get the current node.
            let tracked perm = self.inner.borrow().perms.tracked_borrow(idx as nat);
            let p = ptr.unwrap().borrow(Tracked(perm));

            ptr = p.next;
            idx += 1;
        }

        proof {
            // Now we have ptr == self@[idx] as prev and ptr->next == self@[idx + 1] as this.
            assert(self.wf());
            assert(self.node_wf_at(idx as nat));
            assert(self.node_wf_at((idx + 1) as nat));
        }
        let tracked prev_perm = self.inner.borrow().perms.tracked_borrow(idx as nat);
        let tracked this_perm = self.inner.borrow().perms.tracked_borrow((idx + 1) as nat);

        let prev_node = ptr.unwrap();
        let prev_node_v = prev_node.borrow(Tracked(prev_perm));
        let this_node = prev_node_v.next.unwrap();
        let this_node_v = this_node.borrow(Tracked(this_perm));

        match this_node_v.next {
            // If we have next then we have to update the prev pointer.
            Some(next_node) => {
                proof {
                    assert(self.wf());
                    assert(self.node_wf_at((idx + 2) as nat));
                }

                let tracked mut prev_perm = self.inner.borrow_mut().perms.tracked_remove(
                    idx as nat,
                );
                let tracked mut this_perm = self.inner.borrow_mut().perms.tracked_remove(
                    (idx + 1) as nat,
                );
                let tracked mut next_perm = self.inner.borrow_mut().perms.tracked_remove(
                    (idx + 2) as nat,
                );

                let mut prev_node_v = prev_node.take(Tracked(&mut prev_perm));
                let mut next_node_v = next_node.take(Tracked(&mut next_perm));
                prev_node_v.next = Some(next_node);
                next_node_v.prev = Some(prev_node);

                prev_node.write(Tracked(&mut prev_perm), prev_node_v);
                next_node.write(Tracked(&mut next_perm), next_node_v);
                self.len = self.len - 1;

                // node -> prev    -> this     -> next -> node
                //         ^idx        ^idx + 1   ^ idx + 2
                // node -> prev    -> next     -> node
                //        ^idx        ^idx + 2
                proof {
                    assert(idx + 1 == i);
                    // Update the ghost states.
                    self.inner.borrow_mut().perms.tracked_insert(idx as nat, prev_perm);
                    self.inner.borrow_mut().perms.tracked_insert((idx + 2) as nat, next_perm);
                    self.inner.borrow_mut().ptrs.tracked_remove((idx + 1) as int);

                    assert forall|i: nat|
                        (0 <= i <= idx) || (idx + 2 <= i < old(
                            self,
                        )@.len()) implies self.inner@.perms.dom().contains(i) by {
                        assert(old(self).node_wf_at(i));
                    };

                    // Now we need to shift the key map
                    // [    ] | [    ]
                    //  keep   shift by 1
                    let ghost mut keys_left = Map::new(
                        |i: nat| 0 <= i <= idx as nat,
                        |i: nat| i as nat,
                    );
                    let ghost keys_right = Map::new(
                        |i: nat| idx + 1 <= i < old(self)@.len() - 1,
                        |i: nat| (i + 1) as nat,
                    );

                    let ghost keys = keys_left.union_prefer_right(keys_right);
                    self.inner.borrow_mut().perms.tracked_map_keys_in_place(keys);

                    assert forall|i: nat| (0 <= i <= idx) implies self.node_wf_at(i) by {
                        assert(old(self).node_wf_at(i));
                    };
                    assert forall|i: nat| (idx + 1 <= i < self@.len()) implies self.node_wf_at(
                        i,
                    ) by {
                        assert(old(self).node_wf_at(i + 1));
                    };
                }

                (this_node, Tracked(this_perm))
            },
            None => {
                self.tail = Some(prev_node);
                let tracked mut prev_perm = self.inner.borrow_mut().perms.tracked_remove(
                    idx as nat,
                );
                let tracked mut this_perm = self.inner.borrow_mut().perms.tracked_remove(
                    (idx + 1) as nat,
                );

                let mut prev_node_v = prev_node.take(Tracked(&mut prev_perm));
                prev_node_v.next = None;
                prev_node.write(Tracked(&mut prev_perm), prev_node_v);
                self.len = self.len - 1;

                proof {
                    assert(prev_node == old(self).inner@.ptrs.index(idx as int));
                    assert(idx + 1 == old(self)@.len() - 1);
                    // Update the ghost states.
                    self.inner.borrow_mut().perms.tracked_insert(idx as nat, prev_perm);
                    self.inner.borrow_mut().ptrs.tracked_remove((idx + 1) as int);

                    assert forall|i: nat|
                        0 <= i < self.inner@.ptrs.len() implies #[trigger] self.node_wf_at(i) by {
                        assert(old(self).node_wf_at(i as nat));
                    }
                }

                (this_node, Tracked(this_perm))
            },
        }
    }

    /// If this is missing the trigger cannot be automatically matches by Verus
    pub open spec fn wf(&self) -> bool {
        &&& self.node_wf()
        &&& self.len == self.inner@.ptrs.len()
        &&& if self.inner@.ptrs.len() == 0 {
            &&& self.head.is_none()
            &&& self.tail.is_none()
        } else {
            &&& self.head == Some(self.inner@.ptrs[0])
            &&& self.tail == Some(self.inner@.ptrs[self.inner@.ptrs.len() as int - 1])
        }
    }
}

impl<T> View for LinkedList<T> {
    type V = Seq<T>;

    closed spec fn view(&self) -> Self::V {
        Seq::new(self.inner@.ptrs.len(), |i: int| self.inner@.perms[i as nat].value().value)
    }
}

} // verus!
