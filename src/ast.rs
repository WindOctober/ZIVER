#[derive(Debug)]
pub struct File {
    /// A list of top-level items (imports, constants, structs, components)
    pub items: Vec<Item>,
}

#[derive(Debug)]
pub enum Item {
    /// Represents `import path;`
    Import { path: Vec<String> },
    /// Represents `const <type> <name> = <expr>;`
    Const { ty: Type, name: String, value: Expr },
    /// Represents a `Struct` declaration
    Struct { name: String, fields: Vec<Field> },
    /// Represents a `Component` declaration
    Component { name: String, members: Vec<Member> },
}

#[derive(Debug)]
pub struct Field {
    /// Name and type of the field
    pub name: String,
    pub ty: Type,
}

#[derive(Debug)]
pub enum Member {
    Computation(Func),
    Constraint(Func),
}

#[derive(Debug)]
pub struct Func {
    pub name: String,
    pub params: Vec<Param>,
    pub ret: Option<Type>,
    pub body: Vec<Stmt>,
}

#[derive(Debug)]
pub enum Param {
    SelfParam,
    Typed { name: String, ty: Type },
}

#[derive(Debug)]
pub enum Type {
    /// Basic or user-defined type path
    Path(Vec<String>),
    /// Array type with fixed length expression
    Array(Box<Type>, Expr),
}

#[derive(Debug)]
pub enum Stmt {
    VarDecl {
        ty: Type,
        name: String,
        init: Expr,
    },
    Assign {
        target: LValue,
        value: Expr,
    },
    AndAssign {
        target: LValue,
        value: Expr,
    },
    For {
        var: String,
        start: Expr,
        end: Expr,
        body: Vec<Stmt>,
    },
    AssertBool(Expr),
    AssertEq(Expr, Expr),
    Call {
        callee: LValue,
        args: Vec<Expr>,
    },
    Return(Expr),
}

#[derive(Debug)]
pub struct LValue {
    pub head: Vec<String>,
    pub tails: Vec<LvTail>,
}

#[derive(Debug)]
pub enum LvTail {
    Field(String),
    Index(Expr),
}

#[derive(Debug, Clone)]
pub enum Expr {
    Int(u64),
    Bool(bool),
    Path(Vec<String>),
    Call(Box<Expr>, Vec<Expr>),
    Index(Box<Expr>, Box<Expr>),
    Field(Box<Expr>, String),
    Binary {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Paren(Box<Expr>),
}

#[derive(Debug, Clone, Copy)]
pub enum BinOp {
    Eq,
    Mul,
    Add,
    Sub,
    BitAnd,
}
