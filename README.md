# verus-algebra
Formally verified algebraic trait hierarchies in Rust + Verus.

Defines abstract algebraic interfaces (`Equivalence`, `AdditiveGroup`, `Ring`, `OrderedRing`, `Field`, `OrderedField`) and generic proof lemmas derived from those axioms. Types like `verus-bigint` and `verus-rational` implement these traits.

## Verification

Requires [Verus](https://github.com/verus-lang/verus) built in `../verus/`.

```bash
./scripts/check.sh --require-verus --forbid-trusted-escapes --min-verified 26
```

## License

MIT
