pub mod bindings {
    #![allow(non_upper_case_globals)]
    #![allow(non_camel_case_types)]
    #![allow(non_snake_case)]
    #![allow(dead_code)]
    #![allow(clippy::style)]

    include!(concat!(env!("OUT_DIR"), "/bindings-ccadical-dynamic.rs"));
    // include!("../_bindings-ccadical-dynamic.rs");
}

pub type CCadicalFFI = bindings::ccadical;
pub type CCadicalPtr = *mut bindings::CCaDiCaL;

impl CCadicalFFI {
    pub fn load(name: &str) -> Self {
        unsafe { Self::new(libloading::library_filename(name)) }
            .unwrap_or_else(|e| panic!("Could not load shared library '{}': {}: {:?}", name, e, e))
    }

    pub fn instance() -> &'static Self {
        use ::once_cell::sync::OnceCell;
        static INSTANCE: OnceCell<CCadicalFFI> = OnceCell::new();
        INSTANCE.get_or_init(|| Self::load("cadical"))
    }
}
