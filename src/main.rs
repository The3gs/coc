mod intern;

use std::{collections::HashMap, io::Write, rc::Rc, sync::atomic::AtomicU32};

#[derive(Debug, PartialEq, Eq)]
enum Term {
    Type,
    Var(intern::Token),
    Fun(intern::Token, Option<Rc<Term>>, Rc<Term>),
    FunT(intern::Token, Rc<Term>, Rc<Term>),
    App(Rc<Term>, Rc<Term>),

    Annotation(Rc<Term>, Rc<Term>),
}

enum Value {
    Type,
    Fun(intern::Token, HashMap<intern::Token, Rc<Value>>, Rc<Term>),
    FunT(
        Rc<Value>,
        intern::Token,
        HashMap<intern::Token, Rc<Value>>,
        Rc<Term>,
    ),
    Normal(Rc<Value>, Rc<NormalForm>),
}

enum NormalForm {
    App(Rc<NormalForm>, (Rc<Value>, Rc<Value>)),
    Var(intern::Token),
}

fn val_closure(
    name: intern::Token,
    env: &HashMap<intern::Token, Rc<Value>>,
    body: &Rc<Term>,
    arg: Rc<Value>,
) -> Rc<Value> {
    let mut new_env = env.clone();
    new_env.insert(name, arg);
    body.eval(&new_env)
}

fn gensym() -> u32 {
    static COUNTER: AtomicU32 = AtomicU32::new(0);
    COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

fn ctx_to_env(
    input: HashMap<intern::Token, (Rc<Value>, Option<Rc<Value>>)>,
) -> HashMap<intern::Token, Rc<Value>> {
    input
        .into_iter()
        .map(|(name, (typ, val))| {
            let val = match val {
                Some(val) => val,
                None => Rc::new(Value::Normal(
                    typ.clone(),
                    Rc::new(NormalForm::Var(name.clone())),
                )),
            };
            (name, val)
        })
        .collect()
}

impl Term {
    fn eval(self: &Rc<Self>, env: &HashMap<intern::Token, Rc<Value>>) -> Rc<Value> {
        match self.as_ref() {
            Term::Type => Rc::new(Value::Type),
            Term::Var(s) => env.get(s).unwrap().clone(),
            Term::Fun(name, _arg_t, body) => {
                Rc::new(Value::Fun(name.clone(), env.clone(), body.clone()))
            }
            Term::FunT(name, arg_t, body) => Rc::new(Value::FunT(
                arg_t.eval(env),
                name.clone(),
                env.clone(),
                body.clone(),
            )),
            Term::App(f, a) => {
                let f = f.eval(env);
                let a = a.eval(env);
                f.do_app(a)
            }
            Term::Annotation(_, value) => value.eval(env),
        }
    }

    fn alpha_equiv(&self, other: &Self) -> bool {
        self.alpha_equiv_aux(other, Vec::new(), Vec::new())
    }

    fn alpha_equiv_aux(
        &self,
        other: &Self,
        self_vars: Vec<(intern::Token, u32)>,
        other_vars: Vec<(intern::Token, u32)>,
    ) -> bool {
        match (self, other) {
            (Term::Var(a), Term::Var(b)) => match (
                self_vars.iter().find(|(old, _)| old == a),
                other_vars.iter().find(|(old, _)| old == b),
            ) {
                (None, None) => a == b,
                (Some((_, a)), Some((_, b))) => a == b,
                _ => false,
            },
            (Term::Type, Term::Type) => true,
            (Term::App(a0, b0), Term::App(a1, b1))
            | (Term::Annotation(a0, b0), Term::Annotation(a1, b1)) => {
                a0.alpha_equiv_aux(a1, self_vars.clone(), other_vars.clone())
                    && b0.alpha_equiv_aux(b1, self_vars, other_vars)
            }
            (Term::Fun(name0, _arg_t0, body0), Term::Fun(name1, _arg_t1, body1)) => {
                let id = gensym();
                let mut bigger0 = Vec::new();
                bigger0.push((name0.clone(), id));
                bigger0.extend(self_vars);
                let mut bigger1 = Vec::new();
                bigger1.push((name1.clone(), id));
                bigger1.extend(other_vars);
                body0.alpha_equiv_aux(body1, bigger0, bigger1)
            }
            (Term::FunT(name0, arg_t0, ret_t0), Term::FunT(name1, arg_t1, ret_t1)) => {
                let id = gensym();
                let mut bigger0 = Vec::new();
                bigger0.push((name0.clone(), id));
                bigger0.extend(self_vars.iter().cloned());
                let mut bigger1 = Vec::new();
                bigger1.push((name1.clone(), id));
                bigger1.extend(other_vars.iter().cloned());
                arg_t0.alpha_equiv_aux(arg_t1, self_vars, other_vars)
                    && ret_t0.alpha_equiv_aux(ret_t1, bigger0, bigger1)
            }
            _ => false,
        }
    }

    fn synth(
        self: &Rc<Self>,
        ctx: &HashMap<intern::Token, (Rc<Value>, Option<Rc<Value>>)>,
    ) -> Option<(Rc<Term>, Rc<Term>)> {
        match self.as_ref() {
            Term::Type => Some((self.clone(), self.clone())),
            Term::Var(name) => {
                if let Some((t, _)) = ctx.get(name) {
                    Some((t.read_back(&Rc::new(Value::Type), ctx), self.clone()))
                } else {
                    None
                }
            }
            Term::Fun(name, Some(arg_t), body) => {
                let arg_t_out = arg_t.check(&Rc::new(Value::Type), ctx)?;
                let (ret_t_out, body_out) = body.synth(&extend(
                    ctx,
                    name.clone(),
                    (arg_t_out.eval(&ctx_to_env(ctx.clone())), None),
                ))?;
                Some((
                    Rc::new(Term::FunT(name.clone(), arg_t_out, ret_t_out)),
                    Rc::new(Self::Fun(name.clone(), None, body_out)),
                ))
            }
            Term::FunT(name, arg_t, ret_t) => {
                let arg_t_out = arg_t.check(&Rc::new(Value::Type), ctx)?;
                let ret_t_out = ret_t.check(
                    &Rc::new(Value::Type),
                    &extend(
                        ctx,
                        name.clone(),
                        (arg_t_out.eval(&ctx_to_env(ctx.clone())), None),
                    ),
                )?;
                Some((
                    Rc::new(Term::Type),
                    Rc::new(Term::FunT(name.clone(), arg_t_out, ret_t_out)),
                ))
            }
            Term::App(fun, arg) => {
                let (fun_t, fun_out) = fun.synth(ctx)?;
                match fun_t.eval(&ctx_to_env(ctx.clone())).as_ref() {
                    Value::FunT(arg_t, name, env, ret_t) => {
                        let arg_out = arg.check(&arg_t.clone(), ctx)?;
                        Some((
                            val_closure(*name, env, ret_t, arg_out.eval(&ctx_to_env(ctx.clone())))
                                .read_back(&Rc::new(Value::Type), ctx),
                            Rc::new(Term::App(fun_out, arg_out)),
                        ))
                    }
                    _ => None,
                }
            }
            Term::Annotation(val_t, val) => {
                let val_t_out = val_t.check(&Rc::new(Value::Type), ctx)?;
                let val_out = val.check(&val_t_out.eval(&ctx_to_env(ctx.clone())), ctx)?;

                Some((val_t_out, val_out))
            }
            _ => None,
        }
    }

    fn check(
        self: &Rc<Self>,
        typ: &Rc<Value>,
        ctx: &HashMap<intern::Token, (Rc<Value>, Option<Rc<Value>>)>,
    ) -> Option<Rc<Term>> {
        match self.as_ref() {
            Term::Fun(name0, None, body) => match typ.as_ref() {
                Value::FunT(arg_t, name1, env, ret_t) => {
                    let x_val = Rc::new(Value::Normal(
                        arg_t.clone(),
                        Rc::new(NormalForm::Var(name0.clone())),
                    ));
                    let body_out = body.check(
                        &val_closure(*name1, env, ret_t, x_val),
                        &extend(ctx, name0.clone(), (arg_t.clone(), None)),
                    )?;
                    Some(Rc::new(Term::Fun(name0.clone(), None, body_out)))
                }
                _ => None,
            },
            _ => {
                let (t_out, e_out) = self.synth(ctx)?;
                if Rc::new(Value::Type).convert(ctx, typ, &t_out.eval(&ctx_to_env(ctx.clone()))) {
                    Some(e_out)
                } else {
                    None
                }
            }
        }
    }
}

fn fresh_in<T>(name: intern::Token, env: &HashMap<intern::Token, T>) -> intern::Token {
    let Some(name) = name.get_arc() else {
        return intern::unique();
    };
    let mut name = name.as_ref().to_owned();
    while env.get(&intern::intern(&name)).is_some() {
        name.push('*');
    }
    intern::intern(&name)
}

fn extend<T: Clone>(
    ctx: &HashMap<intern::Token, T>,
    name: intern::Token,
    t: T,
) -> HashMap<intern::Token, T> {
    let mut new = ctx.clone();
    new.insert(name, t);
    new
}

impl Value {
    fn do_app(self: &Rc<Self>, arg: Rc<Self>) -> Rc<Self> {
        match self.as_ref() {
            Value::Fun(name, env, body) => val_closure(*name, env, body, arg),
            Value::Normal(norm_t, norm) => match norm_t.as_ref() {
                Value::FunT(arg_t, name, env, ret_t_body) => Rc::new(Value::Normal(
                    val_closure(*name, env, ret_t_body, arg.clone()),
                    Rc::new(NormalForm::App(norm.clone(), (arg_t.clone(), arg))),
                )),
                _ => panic!("Invalid do_app call"),
            },
            _ => panic!("Invalid do_app call"),
        }
    }

    fn read_back(
        self: &Rc<Value>,
        self_t: &Rc<Value>,
        ctx: &HashMap<intern::Token, (Rc<Value>, Option<Rc<Value>>)>,
    ) -> Rc<Term> {
        match (self_t.as_ref(), self.as_ref()) {
            (Value::FunT(arg_t, name, env, ret_t), f) => {
                let selected_name = if name.get_arc().is_some() {
                    name
                } else {
                    if let Value::Fun(name, _, _) = f {
                        name
                    } else {
                        name
                    }
                };
                let fresh_name = fresh_in(*selected_name, ctx);
                let fresh_name_val = Rc::new(Value::Normal(
                    arg_t.clone(),
                    Rc::new(NormalForm::Var(fresh_name.clone())),
                ));

                Rc::new(Term::Fun(
                    fresh_name.clone(),
                    None,
                    self.do_app(fresh_name_val.clone()).read_back(
                        &val_closure(*name, env, ret_t, fresh_name_val),
                        &extend(ctx, fresh_name, (arg_t.clone(), None)),
                    ),
                ))
            }
            (Value::Type, Value::Type) => Rc::new(Term::Type),
            (Value::Type, Value::FunT(arg_t, name, env, ret_t)) => {
                let fresh_name = fresh_in(*name, ctx);
                Rc::new(Term::FunT(
                    fresh_name.clone(),
                    arg_t.read_back(&Rc::new(Value::Type), ctx),
                    val_closure(
                        *name,
                        env,
                        ret_t,
                        Rc::new(Value::Normal(
                            arg_t.clone(),
                            Rc::new(NormalForm::Var(fresh_name.clone())),
                        )),
                    )
                    .read_back(
                        &Rc::new(Value::Type),
                        &extend(ctx, fresh_name.clone(), (arg_t.clone(), None)),
                    ),
                ))
            }
            (_, Value::Normal(_, ne)) => ne.read_back(ctx),
            _ => panic!("Error reading back value"),
        }
    }

    fn convert(
        self: &Rc<Value>,
        ctx: &HashMap<intern::Token, (Rc<Value>, Option<Rc<Value>>)>,
        a: &Rc<Value>,
        b: &Rc<Value>,
    ) -> bool {
        let e1 = a.read_back(self, ctx);
        let e2 = b.read_back(self, ctx);
        e1.alpha_equiv(&e2)
    }
}

impl NormalForm {
    fn read_back(
        self: &Rc<Self>,
        ctx: &HashMap<intern::Token, (Rc<Value>, Option<Rc<Value>>)>,
    ) -> Rc<Term> {
        match self.as_ref() {
            NormalForm::App(ne, (arg_t, arg)) => {
                Rc::new(Term::App(ne.read_back(ctx), arg.read_back(arg_t, ctx)))
            }
            NormalForm::Var(v) => Rc::new(Term::Var(v.clone())),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Token {
    OpenBracket,
    CloseBracket,
    OpenParen,
    CloseParen,
    Colon,
    ColonEq,
    Comma,
    Ident(intern::Token),
    FatArrow,
    SlimArrow,
}

struct Tokenizer<'a> {
    input: &'a [u8],
    start: usize,
    current: usize,
    tokens: Vec<Token>,
}

impl<'a> Tokenizer<'a> {
    fn new(input: &'a [u8]) -> Self {
        Self {
            input,
            start: 0,
            current: 0,
            tokens: Vec::new(),
        }
    }

    fn advance(&mut self) -> u8 {
        let byte = self.input[self.current];
        self.current += 1;
        byte
    }

    fn peek(&self) -> u8 {
        if self.input.len() > self.current {
            self.input[self.current]
        } else {
            0x00
        }
    }

    fn peek_next(&self) -> u8 {
        if self.input.len() > self.current + 1 {
            self.input[self.current + 1]
        } else {
            0x00
        }
    }

    fn check(&mut self, byte: u8) -> bool {
        if !self.is_at_end() && self.peek() == byte {
            self.advance();
            true
        } else {
            false
        }
    }

    fn scan_token(&mut self) {
        match self.advance() {
            b'(' => self.tokens.push(Token::OpenParen),
            b')' => self.tokens.push(Token::CloseParen),
            b'[' => self.tokens.push(Token::OpenBracket),
            b']' => self.tokens.push(Token::CloseBracket),
            b':' => {
                if self.check(b'=') {
                    self.tokens.push(Token::ColonEq)
                } else {
                    self.tokens.push(Token::Colon)
                }
            }
            b',' => self.tokens.push(Token::Comma),
            whitespace if (whitespace as char).is_ascii_whitespace() => (),
            byte => {
                if byte == b'=' && self.check(b'>') {
                    self.tokens.push(Token::FatArrow)
                } else if byte == b'-' && self.check(b'>') {
                    self.tokens.push(Token::SlimArrow)
                } else {
                    while !self.is_at_end()
                        && match self.peek() {
                            b'(' | b')' | b'[' | b']' | b':' | b',' => false,
                            b'-' | b'=' => self.peek_next() != b'>',
                            byte => !(byte as char).is_ascii_whitespace(),
                        }
                    {
                        self.advance();
                    }
                    self.tokens.push(Token::Ident(intern::intern(
                        std::str::from_utf8(&self.input[self.start..self.current]).unwrap(),
                    )));
                }
            }
        }
    }

    fn is_at_end(&self) -> bool {
        self.current >= self.input.len()
    }

    fn scan_tokens(&mut self) {
        while !self.is_at_end() {
            self.start = self.current;
            self.scan_token()
        }
    }

    pub fn tokenize(input: &'a [u8]) -> Vec<Token> {
        let mut tokenizer = Self::new(input);
        tokenizer.scan_tokens();
        tokenizer.tokens
    }
}

struct Parser {
    tokens: Vec<Token>,
    current: usize,
}

impl Parser {
    fn advance(&mut self) -> Option<&Token> {
        let token = self.tokens.get(self.current);
        self.current += 1;
        token
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.current)
    }

    fn is_at_end(&self) -> bool {
        self.current >= self.tokens.len()
    }

    fn check(&mut self, token: Token) -> bool {
        if self.peek() == Some(&token) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn parse_term(&mut self) -> Option<Rc<Term>> {
        let mut value = match self.advance()? {
            Token::OpenParen => {
                let term = self.parse_term()?;
                if self.check(Token::CloseParen) {
                    term
                } else {
                    return None;
                }
            }
            Token::OpenBracket => {
                let mut args = Vec::new();
                loop {
                    args.push(self.parse_term()?);
                    if self.check(Token::CloseBracket) {
                        break;
                    }
                    if !self.check(Token::Comma) {
                        return None;
                    }
                }
                if self.check(Token::FatArrow) {
                    let mut body = self.parse_term()?;

                    for arg in args.into_iter().rev() {
                        match arg.as_ref() {
                            Term::Var(name) => {
                                body = Rc::new(Term::Fun(*name, None, body));
                            }
                            Term::Annotation(typ, name) => {
                                let Term::Var(name) = name.as_ref() else {
                                    return None;
                                };
                                body = Rc::new(Term::Fun(*name, Some(typ.clone()), body));
                            }
                            _ => return None,
                        }
                    }
                    body
                } else if self.check(Token::SlimArrow) {
                    let mut ret_t = self.parse_term()?;

                    for arg in args.into_iter().rev() {
                        match arg.as_ref() {
                            Term::Annotation(typ, name) => {
                                let Term::Var(name) = name.as_ref() else {
                                    return None;
                                };
                                ret_t = Rc::new(Term::FunT(*name, typ.clone(), ret_t));
                            }
                            _ => ret_t = Rc::new(Term::FunT(intern::unique(), arg, ret_t)),
                        }
                    }

                    ret_t
                } else {
                    return None;
                }
            }
            Token::Ident(name) => Rc::new(Term::Var(name.clone())),
            _ => return None,
        };

        while self.check(Token::OpenParen) {
            loop {
                let arg = self.parse_term()?;
                value = Rc::new(Term::App(value, arg));
                if self.check(Token::CloseParen) {
                    break;
                }
                if !self.check(Token::Comma) {
                    return None;
                }
            }
        }

        if self.check(Token::Colon) {
            let typ = self.parse_term()?;
            value = Rc::new(Term::Annotation(typ, value));
        }

        Some(value)
    }

    fn parse_terms(input: &str) -> Option<Vec<Rc<Term>>> {
        let mut terms = Vec::new();
        let tokens = Tokenizer::tokenize(input.as_bytes());
        let mut parser = Self { tokens, current: 0 };
        while !parser.is_at_end() {
            terms.push(parser.parse_term()?);
        }
        Some(terms)
    }

    fn parse_file(input: &str) -> Option<Vec<(Option<intern::Token>, Rc<Term>)>> {
        let mut terms = Vec::new();
        let tokens = Tokenizer::tokenize(input.as_bytes());
        let mut parser = Self { tokens, current: 0 };
        while !parser.is_at_end() {
            let term = parser.parse_term()?;
            match term.as_ref() {
                Term::Var(name) => {
                    if !parser.check(Token::ColonEq) {
                        terms.push((None, term));
                        continue;
                    }
                    let value = parser.parse_term()?;
                    terms.push((Some(*name), value));
                }
                Term::Annotation(typ, name) => {
                    let Term::Var(name) = name.as_ref() else {
                        terms.push((None, term));
                        continue;
                    };
                    if !parser.check(Token::ColonEq) {
                        terms.push((None, term));
                        continue;
                    }

                    let value = parser.parse_term()?;
                    terms.push((Some(*name), Rc::new(Term::Annotation(typ.clone(), value))));
                }
                _ => terms.push((None, term)),
            }
        }

        Some(terms)
    }
}

fn main() {
    let mut ctx = HashMap::new();
    ctx.insert(
        intern::intern("Type"),
        (Rc::new(Value::Type), Some(Rc::new(Value::Type))),
    );

    let mut args = std::env::args();
    match args.len() {
        1 => {
            let mut count = 0;
            print!("val0 = ");
            std::io::stdout().flush().unwrap();
            for line in std::io::stdin().lines() {
                for term in Parser::parse_terms(&line.unwrap()).unwrap() {
                    if let Some((typ, term_out)) = term.synth(&ctx) {
                        let term_final = term_out
                            .eval(&ctx_to_env(ctx.clone()))
                            .read_back(&typ.eval(&ctx_to_env(ctx.clone())), &ctx);
                        println!("Value");
                        println!("{term_final:?}");
                        println!("Has Type");
                        println!("{typ:?}");
                        ctx.insert(
                            intern::intern(&format!("val{count}")),
                            (
                                typ.eval(&ctx_to_env(ctx.clone())),
                                Some(term_out.eval(&ctx_to_env(ctx.clone()))),
                            ),
                        );

                        count += 1;
                        print!("val{count} = ");
                    } else {
                        println!("Unable to find valid type for {term:?}");
                    }
                }
                std::io::stdout().flush().unwrap();
            }
        }
        2 => {
            let file_name = args.skip(1).next().unwrap();
            let Ok(file) = std::fs::File::open(&file_name) else {
                eprintln!("Error opening file \"{file_name}\"");
                return;
            };

            let input = std::io::read_to_string(file).unwrap();

            for (name, value) in Parser::parse_file(&input).unwrap() {
                match value.synth(&ctx) {
                    Some((type_out, value_out)) => {
                        let value_evaluated = value_out.eval(&ctx_to_env(ctx.clone()));
                        let type_evaluated = type_out.eval(&ctx_to_env(ctx.clone()));
                        if let Some(name) = name {
                            ctx.insert(name, (type_evaluated, Some(value_evaluated)));
                        } else {
                            println!("{:?}", value_evaluated.read_back(&type_evaluated, &ctx));
                        }
                    }
                    None => {
                        println!("Error reading file");
                    }
                }
            }
        }
        _ => println!("Usage: {} [input file]", args.next().unwrap()),
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn parser_tests() {
        use super::*;
        assert_eq!(
            Parser::parse_terms("([t : Type] -> Type) : Type"),
            Some(vec![Rc::new(Term::Annotation(
                Rc::new(Term::Var(intern::intern("Type"))),
                Rc::new(Term::FunT(
                    intern::intern("t"),
                    Rc::new(Term::Var(intern::intern("Type"))),
                    Rc::new(Term::Var(intern::intern("Type")))
                ))
            ))])
        )
    }
}
