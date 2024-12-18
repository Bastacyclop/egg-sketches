
all: test nits

.PHONY: test
test:
	cargo test --features util --release

.PHONY: nits
nits:
	rustup component add rustfmt clippy
	cargo fmt -- --check
	cargo clippy --tests

.PHONY: docs
docs:
	RUSTDOCFLAGS="--cfg docsrs" cargo doc --all-features --open --no-deps