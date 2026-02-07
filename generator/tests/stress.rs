use generator::{create_context, generate_one, NautilusInput};
use libafl::generators::nautilus::NautilusGenerator;
use libafl::generators::Generator;
use libafl::mutators::nautilus::{NautilusRandomMutator, NautilusRecursionMutator};
use libafl::mutators::Mutator;
use libafl::state::NopState;

#[test]
#[ignore]
fn stress_generate_1000_samples() {
    let ctx = create_context(15);
    let mut nautilus_gen = NautilusGenerator::new(&ctx);
    let mut state: NopState<NautilusInput> = NopState::new();

    let mut min_len = usize::MAX;
    let mut max_len = 0usize;
    let mut total_len = 0u64;

    for _ in 0..1000 {
        let input = nautilus_gen
            .generate(&mut state)
            .expect("generate failed");
        let output = generate_one(&ctx, &input);
        let len = output.len();
        min_len = min_len.min(len);
        max_len = max_len.max(len);
        total_len += len as u64;
    }

    let avg_len = total_len as f64 / 1000.0;
    println!("1000 samples at depth 15:");
    println!("  min: {min_len} bytes");
    println!("  max: {max_len} bytes");
    println!("  avg: {avg_len:.0} bytes");

    assert!(
        max_len < 500 * 1024,
        "max sample size {max_len} bytes exceeds 500KB"
    );
}

#[test]
#[ignore]
fn stress_varied_depths() {
    let depths = [3, 5, 10, 15, 20, 30, 50];

    for &depth in &depths {
        let ctx = create_context(depth);
        let mut nautilus_gen = NautilusGenerator::new(&ctx);
        let mut state: NopState<NautilusInput> = NopState::new();

        let mut total_len = 0u64;
        for _ in 0..50 {
            let input = nautilus_gen
                .generate(&mut state)
                .expect(&format!("generate failed at depth {depth}"));
            let output = generate_one(&ctx, &input);
            total_len += output.len() as u64;
        }

        let avg = total_len as f64 / 50.0;
        println!("depth {depth:>3}: avg {avg:.0} bytes (50 samples)");
    }
}

#[test]
#[ignore]
fn stress_mutation_chain_500() {
    let ctx = create_context(15);
    let mut nautilus_gen = NautilusGenerator::new(&ctx);
    let mut state: NopState<NautilusInput> = NopState::new();
    let mut input = nautilus_gen
        .generate(&mut state)
        .expect("generate failed");

    let mut random_mutator = NautilusRandomMutator::new(&ctx);
    let mut recursion_mutator = NautilusRecursionMutator::new(&ctx);

    for i in 0..500 {
        if i % 2 == 0 {
            let _ = random_mutator.mutate(&mut state, &mut input);
        } else {
            let _ = recursion_mutator.mutate(&mut state, &mut input);
        }

        let output = generate_one(&ctx, &input);
        assert!(
            !output.is_empty(),
            "mutation chain step {i} produced empty output"
        );
    }

    let final_output = generate_one(&ctx, &input);
    println!("After 500 mutations: {} bytes", final_output.len());
}
