# Ordered Pool Allocator

[![crates.io](https://img.shields.io/crates/v/ordered-pool-allocator)](https://crates.io/crates/ordered-pool-allocator)
[![ci](https://github.com/george-lim/ordered-pool-allocator/workflows/CI/badge.svg)](https://github.com/george-lim/ordered-pool-allocator/actions)
[![license](https://img.shields.io/github/license/george-lim/ordered-pool-allocator)](https://github.com/george-lim/ordered-pool-allocator/blob/main/LICENSE)

A fast and compact pool allocator with O(1) block access, allocation, and deallocation; as well as O(nlog(n)) block sorting.

This project is a learning exercise to explore how memory pools work and how to optimize for small header size and for specific operations, like sorting memory blocks.

## Design

### Physical vs virtual block indices

To ensure that existing allocated block pointers still point to their respective blocks after sorting, we need to sort block indices instead of the blocks themselves. This means we need to define two types of indices: physical and virtual.

Physical block indices are used to locate the physical block in memory and are fixed. Virtual block indices represent the current virtual order of the blocks in the allocator. These indices should not be stored, as they can point to different physical blocks after sorting or block deallocation. Assuming blocks are never deallocated or sorted, the virtual and physical block indices are guaranteed to be in sync.

### Header

In order to achieve the fastest time complexity for block allocation and deallocation, we need to store three things in addition to the physical blocks:

1. A map of currently allocated virtual block indices to physical block indices (`physical_block_indices`). This allows the allocator to find the correct physical block while performing block indexing.
2. A map of currently allocated physical block indices to virtual block indices (`virtual_block_indices`). This allows the allocator to find the virtual block index to update in O(1) time for the given block pointer during block deallocation.
3. A stack of physical block indices that were previously deallocated. This allows the allocator to find existing deallocated blocks in O(1) time during block allocation.

### Memory Layout

![memory-layout](https://github.com/user-attachments/assets/994064e0-f7ae-44ea-ab9b-1973fdff7985)
