use once_cell::sync::Lazy;
use std::sync::Mutex;
use trybuild::TestCases;

// Fail tests are very sensitive to the rust compiler version.
#[rustversion::any(all(stable, since(1.49)), beta)]
#[test]
fn ui_fail() {
    let t = TEST_CASES.lock().unwrap();
    t.compile_fail("tests/compile-fail/*.rs");
}

#[test]
fn ui_pass() {
    let t = TEST_CASES.lock().unwrap();
    t.pass("tests/compile-pass/*.rs");
}

// Keep singleton TestCases. Using multiple harnesses simultaneously have problems.
// https://github.com/dtolnay/trybuild/issues/58
static TEST_CASES: Lazy<Mutex<TestCases>> = Lazy::new(|| Mutex::new(TestCases::new()));
