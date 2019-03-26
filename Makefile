RUSTC = /home/nwss2/rust/build/x86_64-unknown-freebsd/stage1/bin/rustc
HOME = /home/nwss2
CHERIBUILD = $(HOME)/cheri

lib: libcore_cheri.rlib libcore_cheri.so

libcore_cheri.rlib: lib.rs
	$(RUSTC) $> --crate-type lib --emit=link=$@ -C panic=abort -C debug-assertions=off --target cheri-unknown-freebsd -C linker=$(CHERIBUILD)/output/sdk/bin/cheri-unknown-freebsd-clang -C link-arg=--sysroot=$(CHERIBUILD)/output/sdk/sysroot128 -C link-arg=-fPIC -C target-feature=+soft-float

libcore_cheri.so: lib.rs
	$(RUSTC) $> --crate-type lib --emit=obj=$@ -C panic=abort -C debug-assertions=off --target cheri-unknown-freebsd -C linker=$(CHERIBUILD)/output/sdk/bin/cheri-unknown-freebsd-clang -C link-arg=--sysroot=$(CHERIBUILD)/output/sdk/sysroot128 -C link-arg=-fPIC -C target-feature=+soft-float

clean:
	rm -f *.rlib *.so
