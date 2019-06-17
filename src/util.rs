use hashbrown::HashMap;

lazy_static! {
    pub static ref FUNCTIONS: HashMap<String, fn(f64) -> f64> = {
        let mut map = HashMap::<String, fn(f64) -> f64>::new();
        map.insert("sqrt".into(), f64::sqrt);
        map.insert("cbrt".into(), f64::cbrt);
        map.insert("sin".into(), f64::sin);
        map.insert("cos".into(), f64::cos);
        map.insert("tan".into(), f64::tan);
        map.insert("asin".into(), f64::asin);
        map.insert("acos".into(), f64::acos);
        map.insert("atan".into(), f64::atan);
        map.insert("sinh".into(), f64::sinh);
        map.insert("cosh".into(), f64::cosh);
        map.insert("tanh".into(), f64::tanh);
        map.insert("asinh".into(), f64::asinh);
        map.insert("acosh".into(), f64::acosh);
        map.insert("atanh".into(), f64::atanh);
        map.insert("floor".into(), f64::floor);
        map.insert("ceil".into(), f64::ceil);
        map.insert("abs".into(), f64::abs);
        map.insert("exp".into(), f64::exp);
        map.insert("ln".into(), f64::ln);
        map.insert("log2".into(), f64::log2);
        map.insert("log10".into(), f64::log10);
        map.shrink_to_fit();
        map
    };
}
