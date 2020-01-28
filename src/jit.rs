use hashbrown::HashMap;

use crate::ast::Ast;
use crate::lexer::Lexer;
use cranelift::prelude::*;
use cranelift_module::{DataContext, Linkage, Module};
use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};
use libm::pow;
// use frontend::*;
use std::mem;
use std::slice;

const POW: &str = "pow";

/// The basic JIT class.
pub struct JIT {
    /// The function builder context, which is reused across multiple
    /// FunctionBuilder instances.
    builder_context: FunctionBuilderContext,

    /// The main Cranelift context, which holds the state for codegen. Cranelift
    /// separates this from `Module` to allow for parallel compilation, with a
    /// context per thread, though this isn't in the simple demo here.
    ctx: codegen::Context,

    /// The data context, which is to data objects what `ctx` is to functions.
    data_ctx: DataContext,

    /// The module, with the simplejit backend, which manages the JIT'd
    /// functions.
    module: Module<SimpleJITBackend>,

    /// The parameter names and their indexes for function calls
    required_parameters: HashMap<String, usize>,
}

impl Default for JIT {
    fn default() -> Self {
        // Windows calling conventions are not supported yet.
        if cfg!(windows) {
            unimplemented!();
        }

        let mut builder = SimpleJITBuilder::new(cranelift_module::default_libcall_names());
        let _s = builder.symbol(POW, pow as *const u8);
        let module = Module::new(builder);
        Self {
            builder_context: FunctionBuilderContext::new(),
            ctx: module.make_context(),
            data_ctx: DataContext::new(),
            module,
            required_parameters: HashMap::new(),
        }
    }
}

impl JIT {
    /// Create a new `JIT` instance.
    pub fn new() -> Self {
        Self::default()
    }

    /// Compile a string in the toy language into machine code.
    pub fn compile(
        &mut self,
        input: &str,
    ) -> Result<Box<dyn Fn(HashMap<String, &[f64]>, usize) -> Result<Vec<f64>, String>>, String> {
        // First, parse the string, producing AST nodes.
        // let (name, params, the_return, stmts) =
        //     parser::function(&input).map_err(|e| e.to_string())?;
        let mut lexer = Lexer::new(input);
        let ast = Ast::from_tokens(&mut lexer.parse().map_err(|e| e.to_string())?, "")
            .map_err(|e| e.to_string())?;

        // Then, translate the AST nodes into Cranelift IR.
        self.translate(&ast).map_err(|e| e.to_string())?;

        // Next, declare the function to simplejit. Functions must be declared
        // before they can be called, or defined.
        //
        // TODO: This may be an area where the API should be streamlined; should
        // we have a version of `declare_function` that automatically declares
        // the function?
        let id = self
            .module
            .declare_function(&input, Linkage::Export, &self.ctx.func.signature)
            .map_err(|e| e.to_string())?;

        // Define the function to simplejit. This finishes compilation, although
        // there may be outstanding relocations to perform. Currently, simplejit
        // cannot finish relocations until all functions to be called are
        // defined. For this toy demo for now, we'll just finalize the function
        // below.
        self.module
            .define_function(id, &mut self.ctx)
            .map_err(|e| e.to_string())?;

        // Now that compilation is finished, we can clear out the context state.
        self.module.clear_context(&mut self.ctx);

        // Finalize the functions which we just defined, which resolves any
        // outstanding relocations (patching in addresses, now that they're
        // available).
        self.module.finalize_definitions();

        // We can now retrieve a pointer to the machine code.
        let code = self.module.get_finalized_function(id);

        Ok(Self::dynamic_param_fn(
            code,
            self.required_parameters.clone(),
        ))
    }

    fn dynamic_param_fn(
        function: *const u8,
        required_parameters: HashMap<String, usize>,
    ) -> Box<dyn Fn(HashMap<String, &[f64]>, usize) -> Result<Vec<f64>, String>> {
        // FIXME: Make a macro that will define these for us, maybe up to 256 params
        let keys = required_parameters.keys();
        let mut sorted_keys = vec![];
        for k in keys {
            sorted_keys.push(k.to_owned());
        }
        sorted_keys.sort_unstable();

        match required_parameters.len() {
            0 => {
                let function = unsafe { mem::transmute::<_, fn() -> f64>(function) };
                Box::new(
                    move |_params: HashMap<String, &[f64]>, number_of_evaluations: usize| {
                        let mut results: Vec<f64> = Vec::with_capacity(number_of_evaluations);

                        // We don't just assume this will return the same value in case someone is using a random number generator in a custom function or something similar
                        for _i in 0..number_of_evaluations {
                            results.push(function());
                        }

                        Ok(results)
                    },
                )
            }
            1 => {
                let function = unsafe { mem::transmute::<_, fn(f64) -> f64>(function) };
                Box::new(
                    move |params: HashMap<String, &[f64]>, number_of_evaluations: usize| {
                        let mut results: Vec<f64> = Vec::with_capacity(number_of_evaluations);
                        let param_1 = params.get(&sorted_keys[0]).ok_or(format!("Missing parameter: {}", &sorted_keys[0]))?;

                        // Ensure all the slices have at least as much data as necessary to do the requested number of evaluations
                        for k in &sorted_keys {
                            if number_of_evaluations > params[k].len() {
                                return Err(format!("Missing data for parameter: {}", &sorted_keys[0]));
                            }
                        }

                        for i in 0..number_of_evaluations {
                            results.push(function(param_1[i]));
                        }

                        Ok(results)
                    },
                )
            }
            2 => {
                let function = unsafe { mem::transmute::<_, fn(f64, f64) -> f64>(function) };
                Box::new(
                    move |params: HashMap<String, &[f64]>, number_of_evaluations: usize| {
                        let mut results: Vec<f64> = Vec::with_capacity(number_of_evaluations);
                        let param_1 = params.get(&sorted_keys[0]).ok_or(format!("Missing parameter: {}", &sorted_keys[0]))?;
                        let param_2 = params.get(&sorted_keys[1]).ok_or(format!("Missing parameter: {}", &sorted_keys[1]))?;

                        // Ensure all the slices have at least as much data as necessary to do the requested number of evaluations
                        for k in &sorted_keys {
                            if number_of_evaluations > params[k].len() {
                                return Err(format!("Missing data for parameter: {}", &sorted_keys[0]));
                            }
                        }

                        for i in 0..number_of_evaluations {
                            results.push(function(param_1[i], param_2[i]));
                        }

                        Ok(results)
                    },
                )
            }
            3 => {
                let function = unsafe { mem::transmute::<_, fn(f64, f64, f64) -> f64>(function) };
                Box::new(
                    move |params: HashMap<String, &[f64]>, number_of_evaluations: usize| {
                        let mut results: Vec<f64> = Vec::with_capacity(number_of_evaluations);
                        let param_1 = params.get(&sorted_keys[0]).ok_or(format!("Missing parameter: {}", &sorted_keys[0]))?;
                        let param_2 = params.get(&sorted_keys[1]).ok_or(format!("Missing parameter: {}", &sorted_keys[1]))?;
                        let param_3 = params.get(&sorted_keys[2]).ok_or(format!("Missing parameter: {}", &sorted_keys[2]))?;

                        // Ensure all the slices have at least as much data as necessary to do the requested number of evaluations
                        for k in &sorted_keys {
                            if number_of_evaluations > params[k].len() {
                                return Err(format!("Missing data for parameter: {}", &sorted_keys[0]));
                            }
                        }

                        for i in 0..number_of_evaluations {
                            results.push(function(param_1[i], param_2[i], param_3[i]));
                        }

                        Ok(results)
                    },
                )
            }
            4 => {
                let function =
                    unsafe { mem::transmute::<_, fn(f64, f64, f64, f64) -> f64>(function) };
                Box::new(
                    move |params: HashMap<String, &[f64]>, number_of_evaluations: usize| {
                        let mut results: Vec<f64> = Vec::with_capacity(number_of_evaluations);
                        let param_1 = params.get(&sorted_keys[0]).ok_or(format!("Missing parameter: {}", &sorted_keys[0]))?;
                        let param_2 = params.get(&sorted_keys[1]).ok_or(format!("Missing parameter: {}", &sorted_keys[1]))?;
                        let param_3 = params.get(&sorted_keys[2]).ok_or(format!("Missing parameter: {}", &sorted_keys[2]))?;
                        let param_4 = params.get(&sorted_keys[3]).ok_or(format!("Missing parameter: {}", &sorted_keys[3]))?;

                        // Ensure all the slices have at least as much data as necessary to do the requested number of evaluations
                        for k in &sorted_keys {
                            if number_of_evaluations > params[k].len() {
                                return Err(format!("Missing data for parameter: {}", &sorted_keys[0]));
                            }
                        }

                        for i in 0..number_of_evaluations {
                            results.push(function(param_1[i], param_2[i], param_3[i], param_4[i]));
                        }

                        Ok(results)
                    },
                )
            }
            _ => panic!(),
        }
    }

    /// Create a zero-initialized data section.
    pub fn create_data(&mut self, name: &str, contents: Vec<u8>) -> Result<&[u8], String> {
        // The steps here are analogous to `compile`, except that data is much
        // simpler than functions.
        self.data_ctx.define(contents.into_boxed_slice());
        let id = self
            .module
            .declare_data(name, Linkage::Export, true, None)
            .map_err(|e| e.to_string())?;

        self.module
            .define_data(id, &self.data_ctx)
            .map_err(|e| e.to_string())?;
        self.data_ctx.clear();
        self.module.finalize_definitions();
        let buffer = self.module.get_finalized_data(id);
        // TODO: Can we move the unsafe into cranelift?
        Ok(unsafe { slice::from_raw_parts(buffer.0, buffer.1) })
    }

    fn get_parameters<'a>(ast: &'a Ast, context: &mut Vec<&'a str>) {
        match ast {
            Ast::Variable(name) => {
                context.push(name);
            }
            Ast::Value(_) => {}
            Ast::Function(_, ref arg) => {
                Self::get_parameters(arg, context);
            }
            Ast::Add(ref left, ref right)
            | Ast::Sub(ref left, ref right)
            | Ast::Mul(ref left, ref right)
            | Ast::Div(ref left, ref right)
            | Ast::Exp(ref left, ref right) => {
                Self::get_parameters(left, context);
                Self::get_parameters(right, context);
            }
        }
    }

    // Translate from toy-language AST nodes into Cranelift IR.
    fn translate(&mut self, ast: &Ast) -> Result<(), String> {
        let mut parameter_names = vec![];
        Self::get_parameters(ast, &mut parameter_names);
        parameter_names.sort_unstable();
        parameter_names.dedup();
        for (i, param_name) in parameter_names.iter().enumerate() {
            self.required_parameters.insert((*param_name).to_owned(), i);
        }
        for _p in &parameter_names {
            self.ctx
                .func
                .signature
                .params
                .push(AbiParam::new(types::F64));
        }

        // Our toy language currently only supports one return value, though
        // Cranelift is designed to support more.
        self.ctx
            .func
            .signature
            .returns
            .push(AbiParam::new(types::F64));

        // Create the builder to builder a function.
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        // Create the entry block, to start emitting code in.
        let entry_ebb = builder.create_ebb();

        // Since this is the entry block, add block parameters corresponding to
        // the function's parameters.
        //
        // TODO: Streamline the API here.
        builder.append_ebb_params_for_function_params(entry_ebb);

        // Tell the builder to emit code in this block.
        builder.switch_to_block(entry_ebb);

        // And, tell the builder that this block will have no further
        // predecessors. Since it's the entry block, it won't have any
        // predecessors.
        builder.seal_block(entry_ebb);

        // The toy language allows variables to be declared implicitly.
        // Walk the AST and declare all implicitly-declared variables.
        let variables = declare_variables(&mut builder, &parameter_names, &ast, entry_ebb);

        // Now translate the statements of the function body.
        let mut trans = FunctionTranslator {
            builder,
            variables,
            module: &mut self.module,
        };

        let expression_val = trans.translate_expr(&ast);

        // Set up the return variable of the function. Above, we declared a
        // variable to hold the return value. Here, we just do a use of that
        // variable.
        let return_variable = trans.variables[".the_return"];
        trans.builder.def_var(return_variable, expression_val);
        let return_value = trans.builder.use_var(return_variable);

        // Emit the return instruction.
        trans.builder.ins().return_(&[return_value]);

        // Tell the builder we're done with this function.
        trans.builder.finalize();
        Ok(())
    }
}

/// A collection of state used for translating from toy-language AST nodes
/// into Cranelift IR.
struct FunctionTranslator<'a> {
    builder: FunctionBuilder<'a>,
    variables: HashMap<String, Variable>,
    module: &'a mut Module<SimpleJITBackend>,
}

impl<'a> FunctionTranslator<'a> {
    /// When you write out instructions in Cranelift, you get back `Value`s. You
    /// can then use these references in other instructions.
    fn translate_expr(&mut self, ast: &Ast) -> Value {
        match *ast {
            Ast::Value(val) => self.builder.ins().f64const(Ieee64::with_float(val)),
            Ast::Variable(ref name) => {
                // `use_var` is used to read the value of a variable.
                let variable = self.variables.get(name).expect("variable not defined");
                self.builder.use_var(*variable)
            }
            // Ast::Function(ref func_name, ref args) => self.translate_call(func_name, args),
            Ast::Add(ref left, ref right) => {
                let lhs = self.translate_expr(left);
                let rhs = self.translate_expr(right);
                self.builder.ins().fadd(lhs, rhs)
            }
            Ast::Sub(ref left, ref right) => {
                let lhs = self.translate_expr(left);
                let rhs = self.translate_expr(right);
                self.builder.ins().fsub(lhs, rhs)
            }
            Ast::Mul(ref left, ref right) => {
                let lhs = self.translate_expr(left);
                let rhs = self.translate_expr(right);
                self.builder.ins().fmul(lhs, rhs)
            }
            Ast::Div(ref left, ref right) => {
                let lhs = self.translate_expr(left);
                let rhs = self.translate_expr(right);
                self.builder.ins().fdiv(lhs, rhs)
            }
            Ast::Exp(ref left, ref right) => {
                let lhs = self.translate_expr(left);
                let rhs = self.translate_expr(right);
                self.translate_call(POW, &[lhs, rhs])
            }
            _ => self.builder.ins().f64const(Ieee64::with_float(0.0)),
        }
    }

    fn translate_call(&mut self, name: &str, args: &[Value]) -> Value {
        let mut sig = self.module.make_signature();

        // Add a parameter for each argument.
        for _arg in args {
            sig.params.push(AbiParam::new(types::F64));
        }

        // For simplicity for now, just make all calls return a single I64.
        sig.returns.push(AbiParam::new(types::F64));

        // TODO: Streamline the API here?
        let callee = self
            .module
            .declare_function(name, Linkage::Import, &sig)
            .expect("problem declaring function");
        let local_callee = self
            .module
            .declare_func_in_func(callee, &mut self.builder.func);
        let call = self.builder.ins().call(local_callee, &args);
        self.builder.inst_results(call)[0]
    }

    fn translate_global_data_addr(&mut self, name: String) -> Value {
        let sym = self
            .module
            .declare_data(&name, Linkage::Export, true, None)
            .expect("problem declaring data object");
        let local_id = self
            .module
            .declare_data_in_func(sym, &mut self.builder.func);

        let pointer = self.module.target_config().pointer_type();
        self.builder.ins().symbol_value(pointer, local_id)
    }
}

fn declare_variables(
    builder: &mut FunctionBuilder,
    params: &[&str],
    stmts: &Ast,
    entry_ebb: Ebb,
) -> HashMap<String, Variable> {
    let mut variables = HashMap::new();
    let mut index = 0;

    for (i, name) in params.iter().enumerate() {
        // TODO: cranelift_frontend should really have an API to make it easy to set
        // up param variables.
        let value = builder.ebb_params(entry_ebb)[i];
        let var = declare_variable(builder, &mut variables, &mut index, name);
        builder.def_var(var, value);
    }
    let zero = builder.ins().f64const(Ieee64::with_float(0.0));
    let return_variable = declare_variable(builder, &mut variables, &mut index, ".the_return");
    builder.def_var(return_variable, zero);

    variables
}

/// Declare a single variable declaration.
fn declare_variable(
    builder: &mut FunctionBuilder,
    variables: &mut HashMap<String, Variable>,
    index: &mut usize,
    name: &str,
) -> Variable {
    let var = Variable::new(*index);
    if !variables.contains_key(name) {
        variables.insert(name.into(), var);
        builder.declare_var(var, types::F64);
        *index += 1;
    }
    var
}

#[cfg(test)]
mod tests {
    use super::HashMap;
    use std::process;
    use std::time::Instant;

    #[test]
    fn bench() {
        let watch = Instant::now();
        let mut jit = super::JIT::new();

        // A small test function.
        //
        // The `(c)` declares a return variable; the function returns whatever value
        // it was assigned when the function exits. Note that there are multiple
        // assignments, so the input is not in SSA form, but that's ok because
        // Cranelift handles all the details of translating into SSA form itself.
        let foo_code = "(var1 + var2 * 3) / (2 + 3) - something";

        // Pass the string to the JIT, and it returns a raw pointer to machine code.
        let compiled_formula = jit.compile(&foo_code).unwrap_or_else(|msg| {
            dbg!(msg);
            process::exit(1);
        });

        // And now we can call it!
        // assert_eq!(-16.2, foo(31.0, 11.0, 21.0));

        // let t = Expr::parse("(var1 + var2 * 3) / (2 + 3) - something").unwrap();
        let mut dict: HashMap<String, Vec<f64>> = HashMap::with_capacity(3);
        let capacity = 5_000_000;
        let iterations = 5_000_000;
        dict.insert("var1".to_owned(), Vec::with_capacity(capacity));
        dict.insert("var2".to_owned(), Vec::with_capacity(capacity));
        dict.insert("something".to_owned(), Vec::with_capacity(capacity));
        for i in 1..=iterations {
            dict.get_mut("var1").unwrap().push(10.0 + f64::from(i));
            dict.get_mut("var2").unwrap().push(20.0 + f64::from(i));
            dict.get_mut("something").unwrap().push(30.0 + f64::from(i));
        }
        let dict2: HashMap<String, &[f64]> = dict
            .iter_mut()
            .map(|v| (v.0.to_owned(), v.1.as_slice()))
            .collect();
        let watch = watch.elapsed();

        let watch2 = Instant::now();
        let results = compiled_formula(dict2, capacity);
        let watch2 = watch2.elapsed();

        match results {
            Ok(results) => println!("{}", results[0]),
            Err(msg) => println!("{}", msg)
        }
        println!("{}", watch.as_millis());
        println!("{}", watch2.as_millis());
    }
}
