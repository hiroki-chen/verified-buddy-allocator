# Verified Buddy Allocator

A formally verified implementation of the buddy allocation algorithm in Rust using [Verus](https://github.com/verus-lang/verus), a verification framework that allows developers to write specifications and proofs directly in Rust code.

## Overview

This project provides a memory allocator based on the buddy system algorithm, where memory is managed in blocks that are powers of two in size. The key innovation is that the allocator comes with **formal correctness guarantees** - mathematical proofs that ensure memory safety, prevent double allocation, and maintain proper heap invariants.

### What is a Buddy Allocator?

A buddy allocator manages memory by:
- Dividing memory into blocks of size 2^n
- When a larger block is needed, splitting a larger free block in half
- When freeing memory, attempting to merge with the "buddy" block (the other half of the original block)
- Maintaining free lists for each block size

### Why Formal Verification?

Memory allocators are critical system components where bugs can lead to:
- Memory corruption
- Use-after-free vulnerabilities
- Double allocation errors
- Memory leaks

This implementation uses Verus to provide mathematical certainty that these errors cannot occur.

## Features

- **Formally Verified**: Comes with proofs of memory safety and correctness
- **Configurable**: Supports different heap sizes through const generics
- **No Standard Library**: `#![no_std]` compatible for embedded and kernel development
- **Efficient**: O(log n) allocation and deallocation
- **Thread-Safe Design**: Prepared for concurrent access (when properly synchronized)

## Usage

### Basic Example

```rust
use verified_buddy_allocator::{Buddy, Heap};

// Create a buddy allocator with order 12 (4KB heap)
let mut heap = Buddy::<12>::new();

// Initialize with a memory region
let memory_start = 0x1000_0000u64;
let memory_size = 4096u64;
heap.init(memory_start, memory_size, 12);

// Allocate memory
let ptr = heap.allocate(64, 8); // 64 bytes, 8-byte aligned
if ptr != 0 {
    println!("Allocated memory at: 0x{:x}", ptr);
    
    // Use the memory...
    
    // Deallocate when done
    heap.deallocate(ptr, 64, 8);
}
```

### Configuration

The allocator is configured using const generics:

```rust
// Small heap (2^10 = 1KB maximum)
let small_heap = Buddy::<10>::new();

// Large heap (2^20 = 1MB maximum)  
let large_heap = Buddy::<20>::new();

// Very large heap (2^30 = 1GB maximum)
let huge_heap = Buddy::<30>::new();
```

## Technical Details

### Order and Block Sizes

The `ORDER` const generic parameter determines:
- Maximum heap size: 2^ORDER bytes
- Number of free lists: ORDER
- Minimum block size: heap_size / 2^(ORDER-1)

### Memory Layout Requirements

- Heap size must be a power of 2
- Heap must be aligned to `HEAP_ALIGNMENT` (4KB)
- Minimum block size must be at least `size_of::<Node<()>>()`

### Verification Specifications

The implementation includes formal specifications for:

- **Memory Safety**: Allocated pointers are always within heap bounds
- **No Double Allocation**: The same memory cannot be allocated twice
- **Proper Alignment**: All allocations respect alignment requirements
- **Block Invariants**: Free lists maintain proper ordering and non-overlapping blocks
- **Buddy Relationships**: Block splitting and merging preserves buddy properties

## Use Cases

This allocator is particularly suitable for:

- **Kernel Development**: OS kernels requiring verified memory management
- **Embedded Systems**: Resource-constrained environments needing safety guarantees
- **Safety-Critical Software**: Applications where memory corruption is unacceptable
- **Research**: Academic work on verified systems programming

## Limitations

- Requires Verus for full verification
- `#![no_std]` environment (no standard library)
- Fixed heap size determined at compile time
- Internal fragmentation due to power-of-2 block sizes

## Contributing

1. Fork the repository
2. Create a feature branch
3. Ensure all verification conditions pass
4. Submit a pull request

## License

This project is licensed under the terms specified in the LICENSE file.
