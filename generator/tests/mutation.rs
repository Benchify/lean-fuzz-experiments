use generator::{create_context, generate_one, NautilusInput};
use libafl::generators::nautilus::NautilusGenerator;
use libafl::generators::Generator;
use libafl::mutators::nautilus::{NautilusRandomMutator, NautilusRecursionMutator};
use libafl::mutators::Mutator;
use libafl::state::NopState;

fn make_seed(ctx: &generator::NautilusContext) -> (NautilusInput, NopState<NautilusInput>) {
    let mut nautilus_gen = NautilusGenerator::new(ctx);
    let mut state: NopState<NautilusInput> = NopState::new();
    let input = nautilus_gen.generate(&mut state).expect("generate failed");
    (input, state)
}

#[test]
fn random_mutation_100x_no_panic() {
    let ctx = create_context(15);
    let (mut input, mut state) = make_seed(&ctx);
    let mut mutator = NautilusRandomMutator::new(&ctx);

    for i in 0..100 {
        let _ = mutator.mutate(&mut state, &mut input);
        let output = generate_one(&ctx, &input);
        assert!(
            !output.is_empty(),
            "random mutation {i} produced empty output"
        );
    }
}

#[test]
fn recursion_mutation_100x_no_panic() {
    let ctx = create_context(15);
    let (mut input, mut state) = make_seed(&ctx);
    let mut mutator = NautilusRecursionMutator::new(&ctx);

    for i in 0..100 {
        let _ = mutator.mutate(&mut state, &mut input);
        let output = generate_one(&ctx, &input);
        assert!(
            !output.is_empty(),
            "recursion mutation {i} produced empty output"
        );
    }
}

#[test]
fn mutation_preserves_utf8() {
    let ctx = create_context(15);
    let mut nautilus_gen = NautilusGenerator::new(&ctx);
    let mut state: NopState<NautilusInput> = NopState::new();
    let mut random_mutator = NautilusRandomMutator::new(&ctx);
    let mut recursion_mutator = NautilusRecursionMutator::new(&ctx);

    for seed_idx in 0..5 {
        let mut input = nautilus_gen
            .generate(&mut state)
            .expect("generate failed");
        for mutation_idx in 0..20 {
            // Alternate between random and recursion mutators
            if mutation_idx % 2 == 0 {
                let _ = random_mutator.mutate(&mut state, &mut input);
            } else {
                let _ = recursion_mutator.mutate(&mut state, &mut input);
            }
            let output = generate_one(&ctx, &input);
            assert!(
                !output.contains('\u{FFFD}'),
                "seed {seed_idx}, mutation {mutation_idx}: output contains replacement character"
            );
        }
    }
}
