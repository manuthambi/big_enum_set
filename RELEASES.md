# Version 1.0.0 (Unreleased)
* Added BigEnumSet::from_bits_safe().

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
