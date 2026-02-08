use generator::{create_context, generate_one, NautilusInput};
use libafl::generators::nautilus::NautilusGenerator;
use libafl::generators::Generator;
use libafl::state::NopState;

fn generate_samples(depth: usize, count: usize) -> Vec<String> {
    let ctx = create_context(depth);
    let mut nautilus_gen = NautilusGenerator::new(&ctx);
    let mut state: NopState<NautilusInput> = NopState::new();

    (0..count)
        .map(|_| {
            let input = nautilus_gen.generate(&mut state).expect("generate failed");
            generate_one(&ctx, &input)
        })
        .collect()
}

#[test]
fn generate_produces_nonempty_utf8() {
    let samples = generate_samples(15, 10);
    for (i, s) in samples.iter().enumerate() {
        assert!(!s.is_empty(), "sample {i} is empty");
        // String::from_utf8_lossy replaces invalid sequences with U+FFFD
        assert!(
            !s.contains('\u{FFFD}'),
            "sample {i} contains replacement character (invalid UTF-8)"
        );
    }
}

#[test]
fn generate_reasonable_length() {
    let samples = generate_samples(15, 50);
    for (i, s) in samples.iter().enumerate() {
        assert!(
            s.len() < 100 * 1024,
            "sample {i} is {} bytes, exceeds 100KB",
            s.len()
        );
    }
}

#[test]
fn depth_affects_output_size() {
    let shallow = generate_samples(5, 30);
    let deep = generate_samples(30, 30);

    let shallow_avg: f64 =
        shallow.iter().map(|s| s.len() as f64).sum::<f64>() / shallow.len() as f64;
    let deep_avg: f64 = deep.iter().map(|s| s.len() as f64).sum::<f64>() / deep.len() as f64;

    // Deep should produce larger output on average
    assert!(
        deep_avg > shallow_avg,
        "expected depth 30 avg ({deep_avg:.0}) > depth 5 avg ({shallow_avg:.0})"
    );
}

#[test]
fn generated_output_contains_lean_keywords() {
    let samples = generate_samples(15, 20);
    let combined: String = samples.join("\n");

    let keywords = ["def", "theorem", "Nat", ":=", "Type"];
    for kw in &keywords {
        assert!(
            combined.contains(kw),
            "keyword '{kw}' never appeared across 20 generated samples"
        );
    }
}

#[test]
fn escaped_braces_produce_literal_braces() {
    // The grammar uses \{...\} for Lean implicit binders. After Nautilus
    // unparsing, these should become literal { and } in the output.
    let samples = generate_samples(15, 50);
    let combined: String = samples.join("\n");

    assert!(
        combined.contains('{') || combined.contains('}'),
        "no literal braces found in 50 generated samples — escaped braces may be broken"
    );
}
