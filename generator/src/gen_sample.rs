use generator::{create_context, generate_one, NautilusInput};
use libafl::generators::nautilus::NautilusGenerator;
use libafl::generators::Generator;
use libafl::state::NopState;

fn main() {
    let depth: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(15);
    let ctx = create_context(depth);
    let mut generator = NautilusGenerator::new(&ctx);
    let mut state: NopState<NautilusInput> = NopState::new();
    let input = generator.generate(&mut state).expect("generation failed");
    print!("{}", generate_one(&ctx, &input));
}
