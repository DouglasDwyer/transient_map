# transient_map

[![Crates.io](https://img.shields.io/crates/v/transient_map.svg)](https://crates.io/crates/transient_map)
[![Docs.rs](https://docs.rs/transient_map/badge.svg)](https://docs.rs/transient_map)

`TransientMap` acts as a wrapper for `std::collections::HashMap` which allows for
the eviction of unused elements. In addition to the standard hashmap API, it provides
the following extra functions:

- `drain_unused` removes all of the elements that have not been inserted or accessed
since the previous drain call, returning the elements as an iterator. The entirety of
the drain operation takes `O(unused elements)` time. Note that this is faster
than the amount of time required to iterate over the entire map, which is `O(capacity)`.
- `drain_used` removes all of the elements that have been inserted or accessed since
the last drain call. The entirety of the drain operation takes `O(used elements)` time.
- `set_all_used` marks all elements as having been accessed in `O(1)` time.
- `set_all_unused` marks all elements as not having been accessed in `O(1)` time.

These additional functions make `TransientMap` an ideal choice for applications like
caching, where it is desirable to efficiently discard data that has not been used.

The following is a brief example of how to use `TransientMap`:

```rust
let mut map = TransientMap::new();
map.insert_unused(1, "a");
map.insert_unused(2, "b");
assert_eq!(Some("b"), map.remove(&2));
map.insert(3, "c");
map.insert(4, "d");
assert_eq!(vec!((1, "a")), map.drain_unused().collect::<Vec<_>>());

let mut res = map.drain_unused().collect::<Vec<_>>();
res.sort_by(|a, b| a.0.cmp(&b.0));

assert_eq!(vec!((3, "c"), (4, "d")), res);
assert_eq!(0, map.len());
```