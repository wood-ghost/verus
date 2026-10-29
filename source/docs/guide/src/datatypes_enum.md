## Enum

In Verus, just as in Rust, you can use `enum` to define a datatype that is any one of the
defined variants:
```rust
{{#include ../../../../examples/guide/datatypes.rs:beverage}}
```

An `enum` is often used just for its tags, without member fields:
```rust
{{#include ../../../../examples/guide/datatypes.rs:syrup}}
```

## Identifying a variant with the `is` operator

In spec contexts, the `is` operator lets you query which variant of an
enum a variable contains.
```rust
{{#include ../../../../examples/guide/datatypes.rs:make_float}}
```

The syntax `!is` is a shorthand for `!(.. is ..)`.

## Accessing fields with the arrow operator

If all the fields have distinct names, as in the `Beverage` example,
you can refer to fields with the arrow `->` operator:
```rust
{{#include ../../../../examples/guide/datatypes.rs:count_creamers}}
```

If an `enum` field reuses a name, you can qualify the field access:
```rust
{{#include ../../../../examples/guide/datatypes.rs:life}}
```

`match` works as in Rust.
```rust
{{#include ../../../../examples/guide/datatypes.rs:shape}}
```

For variants like `Shape` declared with round parentheses `()`,
you can use Verus's `->` tuple-like syntax to access a single field
without a match destruction:
```rust
{{#include ../../../../examples/guide/datatypes.rs:rect_height}}
```

## Let-chains (Rust 2024)

With Rust edition 2024, `if` and `while` conditions can combine pattern matches
and boolean expressions using `&&`. Pass `--edition=2024` to Verus, or set
`edition = "2024"` in your crate's `Cargo.toml`.

```rust
use vstd::prelude::*;

verus! {
fn positive(value: Option<u32>) -> (r: bool)
    ensures r == match value { Some(x) => x > 0, None => false },
{
    if let Some(x) = value && x > 0 {
        return true;
    }
    false
}

fn main() {}
}
```

Conditions are evaluated from left to right, stopping at the first false
expression or unsuccessful pattern. A pattern's bindings are available to later
conditions and the successful body, but not the `else` branch. Moves and borrows
take place when the pattern succeeds, even if a later condition fails.

Like existing `while let` loops, let-chain loops use a conditional break
internally. Use loop `ensures` clauses to establish exit properties, and
`invariant_except_break` for invariants that need not hold after evaluating an
exiting condition.

## matches with &&, ==>, and &&&

`match` is natural for examining every variant of an `enum`.
If you'd like to bind the fields while only considering one or two of the
variants, you can use Verus's `matches` syntax:
```rust
{{#include ../../../../examples/guide/datatypes.rs:cuddly}}
```

Because the `matches` syntax binds names in patterns, it has no trouble
with field names reused across variants, so it may be preferable
to the (qualified) arrow syntax.

Notice that `l matches Mammal { legs, .. } && legs == 4` is a boolean expression,
with the special property that `legs` is bound in the remainder of the
expression after `&&`. That helpful binding also works with `==>`
and `&&&`:
```rust
{{#include ../../../../examples/guide/datatypes.rs:kangaroo}}
```
