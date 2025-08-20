# Changelog

## Unreleased

## [v0.5.0][] (2025-08-21)

- Update `heapless` to version `0.9.1` ([#11][])
- Add support for heapless's `View` types ([#11][])
- Move to `serde_core` ([#11][])

## [v0.4.0][] (2024-06-20)

- Update `heapless` to version `0.8` ([#3][])
- Remove the `Deref` implementation to `heapless` and implement `Deref<Target = [u8]>` directly ([#8][])
- Add conversions between `[u8; N]` and `heapless::Vec<u8, N>`. The `heapless` conversions are behind the `heapless-0.8` feature flag so that `heapless` can be bumped without a semver-breaking change in the future ([#6][] and [#8][])
- Add `Bytes::increase_capacity` ([#6][])

[v0.5.0]: https://github.com/trussed-dev/heapless-bytes/releases/tag/0.5.0
[v0.4.0]: https://github.com/trussed-dev/heapless-bytes/releases/tag/0.4.0
[#3]: https://github.com/trussed-dev/heapless-bytes/pull/3
[#6]: https://github.com/trussed-dev/heapless-bytes/pull/6
[#8]: https://github.com/trussed-dev/heapless-bytes/pull/8
[#11]: https://github.com/trussed-dev/heapless-bytes/pull/11


