# Version 0.2.0 (2020-05-10)

## Breaking changes
* **[WARNING: Potential silent breaking change]** Changed `BigEnumSet::insert` to
  return whether a value was newly  inserted, rather than whether the value
  already existed in the set. This corresponds better with the behavior of
  `HashSet::insert` and `BTreeSet::insert`. This change matches a similar change
  in `EnumSet` in `enumset` crate version 1.0.
* Updated the signatures of many methods in `BigEnumSet` to take arguments by
  value or reference. Pass the value by reference to avoid copies, if the enum set is
  large. Also, operator implementations for `BigEnumSet` take arguments by value or
  reference.
* Removed `Copy`, `PartialOrd`, `Ord`, `PartialEq`,
  `Eq` and `Hash` implementations of `EnumSetIter`. They are typically not useful
  for iterators and might result in undetected bugs in client code. This change
  matches a similar change in `EnumSet` in `enumset` crate version 1.0.
* Renamed `BigEnumSet::to_bits` to `BigEnumSet::as_bits`.
* Replaced `BigEnumSet::from_bits` with `BigEnumSet::try_from_bits`,
  which returns `Option<BigEnumSet>`.
* Removed `nightly` feature flag, as it is no longer required.

## New features
* Added `BigEnumSet::from_bits_truncated` that truncate unknown bits.

## Bugfixes
* More exhaustive checking to ensure that any unused trailing bytes at
  the end of a serialized enum are zero, when `#[big_enum_set(serialize_deny_unknown)]`
  is set.
* Proc macro now supports `#[repr(XXX)]` annontations. The variant discriminants should
  still be non-negative and fit in a `u16`.

# Version 0.1.7 (2020-03-13)
* Fixed a compilation breakage with 0.1.6

# Version 0.1.6 (2020-03-13) YANKED
* Fixed a bug where compilation failed when the `serde` flag was enabled, and
  another trait that defined `serialize` or `deserialize` was in scope.
* Minor code cleanups.

# Version 0.1.5 (2019-12-19)
* Added documentation for derive macro.

# Version 0.1.4 (2019-12-19)
* Fixed a bug where `#[enumset(serialize_as_list)]` did not work when `Result`
  is shadowed.
* Manually implement `Hash`, `PartialOrd`, and `Ord` instead of deriving them.
  This allows `BigEnumSet` to have those traits implemented even when the enum
  itself does not.

# Version 0.1.3 (2019-10-02)
* Implemented `Extend` and `FromIterator` for `BigEnumSet<T>`.

# Version 0.1.2 (2019-10-02)
* Updated dependencies to newer versions.
* Removed `big_enum_set::internal::core_export` and directly use `::core` in macros.
* Enable CI using TravisCI.

# Version 0.1.1 (2019-10-02)
* Fixed a bug so that empty enums and enums with one enum compiles.

# Version 0.1.0 (2019-09-24)
* Initial version based on a fork of Lymia/enumset.
