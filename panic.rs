#![unstable(feature = "core_panic_info",
            reason = "newly available in libcore",
            issue = "44489")]

use marker::PhantomData;

#[lang = "panic_info"]
#[stable(feature = "panic_hooks", since = "1.10.0")]
pub struct PanicInfo<'a> {
    phantom: PhantomData<&'a ()>,
}
