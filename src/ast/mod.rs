pub mod helpers;

#[derive(Debug, Clone)]
pub struct File {
    /// A list of top-level items (imports, constants, structs, components)
    pub items: Vec<Item>,
}

#[derive(Debug, Clone)]
pub enum Item {
    // `import path;`
    Import {
        id: Option<i64>,
        path: Vec<String>,
    },

    // `Enum ...`
    Enum {
        id: Option<i64>,
        name: String,
        variants: Vec<EnumVariant>,
    },

    // `const <type> <name> = <expr>;`
    Const {
        id: Option<i64>,
        ty: Type,
        name: String,
        value: Expr,
    },

    // `Struct ...`
    Struct {
        id: Option<i64>,
        name: String,
        fields: Vec<Field>,
    },

    // `Component ...`
    Component {
        id: Option<i64>,
        name: String,
        members: Vec<Member>,
        query: Option<Query>,
    },

    // Top-level free function: `fn name(params) { ... }`
    Function {
        id: Option<i64>,
        func: Func,
    },
}

/// Single enum variant with an optional explicit discriminant.
#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub id: Option<i64>,
    pub name: String,
    pub value: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IOType {
    Input,
    Output,
}

#[derive(Debug, Clone)]
pub struct Field {
    // Field declaration id
    pub id: Option<i64>,
    pub io: IOType,
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub enum Member {
    Computation(Func),
    Constraint(Func),
}

#[derive(Debug, Clone)]
pub struct Func {
    // Function declaration id
    pub id: Option<i64>,
    pub name: String,
    pub params: Vec<Param>,
    pub ret: Option<Type>,
    pub body: Vec<Stmt>,
}

#[derive(Debug, Clone)]
pub enum Param {
    // `self` binding id
    SelfParam {
        id: Option<i64>,
    },
    // parameter binding id
    Typed {
        id: Option<i64>,
        name: String,
        ty: Type,
        io: IOType,
    },
}

#[derive(Debug, Clone)]
pub struct Query {
    pub lhs: Vec<Vec<String>>, // list of paths
    pub rhs: Vec<Vec<String>>, // list of paths
}

#[derive(Debug, Clone)]
pub enum Type {
    /// Named type; `ref_id` resolves to the unique id of the type (e.g., a struct).
    Path {
        segments: Vec<String>,
        ref_id: Option<i64>,
    },
    /// Tuple type, retaining element types in order.
    Tuple(Vec<Type>),
    /// Array type
    Array(Box<Type>, Expr),
    /// Map type with (timestamp, key, value) sub-types.
    Map {
        timestamp: Box<Type>,
        key: Box<Type>,
        value: Box<Type>,
    },
    /// First-class function type; `ref_id` resolves to the function declaration id.
    Function { ref_id: Option<i64> },
}

#[derive(Debug, Clone)]
pub enum Stmt {
    VarDecl {
        // variable binding id
        id: Option<i64>,
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
        // loop variable binding id
        id: Option<i64>,
        var: String,
        start: Expr,
        end: Expr,
        body: Vec<Stmt>,
    },
    If {
        cond: Expr,
        then_branch: Vec<Stmt>,
        else_branch: Vec<Stmt>,
    },
    AssertBool(Expr),
    AssertEq(Expr, Expr),
    AssertZero(Expr),
    AssertRange {
        value: Expr,
        ty: Type,
    },
    Lookup {
        chip: Vec<String>,
        opcode: Expr,
        args: Vec<Expr>,
    },
    Call {
        callee: LValue,
        args: Vec<Expr>,
    },
    Return(Expr),
}

#[derive(Debug, Clone)]
pub struct LValue {
    // head reference (variable/func) ref_id
    pub ref_id: Option<i64>,
    pub head: Vec<String>,
    pub tails: Vec<LvTail>,
}

#[derive(Debug, Clone)]
pub enum LvTail {
    // field access
    Field { name: String },
    Index(Expr),
    MapIndex(Expr, Expr), // two-key map index (timestamp, addr)
}

#[derive(Debug, Clone)]
pub enum Expr {
    Int(u64),
    Bool(bool),

    // name reference with ref_id (var/const/func etc.)
    Path {
        segments: Vec<String>,
        ref_id: Option<i64>,
    },

    Call(Box<Expr>, Vec<Expr>),
    Index(Box<Expr>, Box<Expr>),
    /// Map access with a tuple key (timestamp, address).
    MapIndex {
        base: Box<Expr>,
        keys: Vec<Expr>, // expected arity: 2
    },

    // field access with ref_id to Field
    Field {
        base: Box<Expr>,
        name: String,
        ref_id: Option<i64>,
    },

    Binary {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Paren(Box<Expr>),
}

/// Binary operators in the DSL.
#[derive(Debug, Clone, Copy)]
pub enum BinOp {
    // Comparisons
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,

    // Arithmetic
    Mul,
    Add,
    Sub,

    // Bitwise and logical
    BitAnd,
    And, // &&
    Or,  // ||
}
