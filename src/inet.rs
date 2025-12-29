use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct VertexId(usize);

#[derive(Clone, Debug)]
pub struct Edge<T> {
    pub src: VertexId,
    pub dst: VertexId,
    pub tag: T,
}

#[derive(Clone, Debug)]
pub struct Graph<T> {
    next_id: usize,
    edges: Vec<Edge<T>>,
}

impl<T: Clone> Graph<T> {
    pub fn new() -> Self {
        Graph {
            next_id: 0,
            edges: Vec::new(),
        }
    }

    pub fn alloc_vertex(&mut self) -> VertexId {
        let id = VertexId(self.next_id);
        self.next_id += 1;
        id
    }

    pub fn add_edge(&mut self, src: VertexId, dst: VertexId, tag: T) {
        self.edges.push(Edge { src, dst, tag });
    }

    pub fn get_outgoing(&self, vertex: VertexId) -> Vec<(T, VertexId)> {
        self.edges
            .iter()
            .filter(|e| e.src == vertex)
            .map(|e| (e.tag.clone(), e.dst))
            .collect()
    }

    pub fn get_incoming(&self, vertex: VertexId) -> Vec<(VertexId, T)> {
        self.edges
            .iter()
            .filter(|e| e.dst == vertex)
            .map(|e| (e.src, e.tag.clone()))
            .collect()
    }

    pub fn remove_vertex(&mut self, vertex: VertexId) {
        self.edges.retain(|e| e.src != vertex && e.dst != vertex);
    }

    pub fn merge_vertices(&mut self, old: VertexId, new: VertexId) {
        for e in &mut self.edges {
            if e.src == old {
                e.src = new;
            }
            if e.dst == old {
                e.dst = new;
            }
        }
    }

    pub fn alloc_vertex2(&mut self, (t1, v1): (T, VertexId), (t2, v2): (T, VertexId)) -> VertexId {
        let new_v = self.alloc_vertex();
        self.add_edge(new_v, v1, t1);
        self.add_edge(new_v, v2, t2);
        new_v
    }
}

fn all_pairs<T: Clone>(items: &[T]) -> Vec<(T, T)> {
    let mut pairs = Vec::new();
    for (i, x) in items.iter().enumerate() {
        for y in &items[i + 1..] {
            pairs.push((x.clone(), y.clone()));
        }
    }
    pairs
}

// Tags

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SubTag {
    Arg,
    Ret,
    TupI(usize),
    DupI(usize),
    TagData(String),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum RawTag {
    TFun,
    TPair,
    TDup(String),
    TData,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Polarity {
    Constructor,
    Destructor,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Tag {
    pub raw: RawTag,
    pub sub: SubTag,
    pub polarity: Polarity,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Interaction {
    Annihilate,
    Ignore,
    Commute,
    Stuck,
}

impl RawTag {
    fn is_dup(&self) -> bool {
        matches!(self, RawTag::TDup(_))
    }

    fn same_as(&self, other: &RawTag) -> bool {
        match (self, other) {
            (RawTag::TFun, RawTag::TFun) => true,
            (RawTag::TPair, RawTag::TPair) => true,
            (RawTag::TData, RawTag::TData) => true,
            (RawTag::TDup(v1), RawTag::TDup(v2)) => v1 == v2,
            _ => false,
        }
    }
}

impl Tag {
    pub fn relation(&self, other: &Tag) -> Interaction {
        if self.raw.same_as(&other.raw) {
            if self.sub == other.sub {
                Interaction::Annihilate
            } else {
                Interaction::Ignore
            }
        } else if self.raw.is_dup() || other.raw.is_dup() {
            Interaction::Commute
        } else {
            Interaction::Stuck
        }
    }
}

// Sharing Graph

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct VarName(pub String);

#[derive(Clone, Debug)]
pub struct SharingGraph {
    pub graph: Graph<Tag>,
    pub root: VertexId,
    pub free_vars: HashMap<VarName, Vec<VertexId>>,
}

pub type Remap = Vec<(VertexId, VertexId)>;

fn apply_remap(remap: &Remap, v: VertexId) -> VertexId {
    remap
        .iter()
        .find(|(old, _)| *old == v)
        .map(|(_, new)| *new)
        .unwrap_or(v)
}

#[derive(Debug)]
pub enum INetError {
    Stuck(Tag, Tag),
    FuelExceeded,
    TooManyOutgoingEdges,
}

impl SharingGraph {
    pub fn merge_vertices(&mut self, old: VertexId, new: VertexId) {
        self.graph.merge_vertices(old, new);
        if self.root == old {
            self.root = new;
        }
        for vertices in self.free_vars.values_mut() {
            for v in vertices.iter_mut() {
                if *v == old {
                    *v = new;
                }
            }
        }
    }

    pub fn protected_vertices(&self) -> Vec<VertexId> {
        let mut protected = vec![self.root];
        for vertices in self.free_vars.values() {
            protected.extend(vertices);
        }
        protected
    }

    pub fn is_protected(&self, v: VertexId) -> bool {
        self.protected_vertices().contains(&v)
    }

    pub fn eliminate_cut(&mut self, v: VertexId) -> Result<Remap, INetError> {
        let incoming = self.graph.get_incoming(v);
        let pairs = all_pairs(&incoming);
        self.graph.remove_vertex(v);

        let mut remap: Remap = Vec::new();
        for ((v1, t1), (v2, t2)) in pairs {
            let v1 = apply_remap(&remap, v1);
            let v2 = apply_remap(&remap, v2);
            match t1.relation(&t2) {
                Interaction::Ignore => {}
                Interaction::Annihilate => {
                    self.merge_vertices(v2, v1);
                    remap.push((v2, v1));
                }
                Interaction::Commute => {
                    self.graph.alloc_vertex2((t2, v1), (t1, v2));
                }
                Interaction::Stuck => return Err(INetError::Stuck(t1, t2)),
            }
        }
        Ok(remap)
    }

    pub fn eval(
        &mut self,
        protected: &mut Vec<VertexId>,
        curr: VertexId,
        fuel: usize,
    ) -> Result<(Remap, bool), INetError> {
        if fuel == 0 {
            return Err(INetError::FuelExceeded);
        }

        let outgoing = self.graph.get_outgoing(curr);
        match outgoing.len() {
            1 => {
                let next = outgoing[0].1;
                let (remap, changed) = self.eval(protected, next, fuel - 1)?;
                if changed {
                    for v in protected.iter_mut() {
                        *v = apply_remap(&remap, *v);
                    }
                    let curr = apply_remap(&remap, curr);
                    self.eval(protected, curr, fuel - 1)
                } else {
                    Ok((remap, false))
                }
            }
            0 => {
                if protected.contains(&curr) {
                    Ok((Vec::new(), false))
                } else {
                    let remap = self.eliminate_cut(curr)?;
                    Ok((remap, true))
                }
            }
            2 => Ok((Vec::new(), false)),
            _ => Err(INetError::TooManyOutgoingEdges),
        }
    }

    pub fn whnf(&mut self) -> Result<(), INetError> {
        let mut protected = self.protected_vertices();
        let root = self.root;
        self.eval(&mut protected, root, 10000)?;
        Ok(())
    }

    pub fn nf(&mut self) -> Result<(), INetError> {
        self.whnf()?;
        let incoming: Vec<VertexId> = self
            .graph
            .get_incoming(self.root)
            .into_iter()
            .map(|(v, _)| v)
            .collect();
        let mut protected = self.protected_vertices();
        protected.extend(&incoming);

        for v in incoming {
            self.eval(&mut protected, v, 10000)?;
        }
        Ok(())
    }
}

// Translation from Expr to SharingGraph

use crate::expr::{Expr, FunMode, Pat};

type TranslateEnv = HashMap<VarName, Vec<VertexId>>;

fn env_remove(env: &mut TranslateEnv, param: &VarName) -> Vec<VertexId> {
    env.remove(param).unwrap_or_default()
}

fn merge_env(env1: TranslateEnv, mut env2: TranslateEnv) -> TranslateEnv {
    for (k, mut v) in env1 {
        env2.entry(k).or_default().append(&mut v);
    }
    env2
}

#[derive(Debug)]
pub enum TranslateError {
    LinearParamNotUsedOnce { param: String, uses: usize },
    ExpectedVarPattern,
}

fn connect_param(
    graph: &mut Graph<Tag>,
    fun_nid: VertexId,
    param: &str,
    uses: Vec<VertexId>,
    mode: FunMode,
) -> Result<(), TranslateError> {
    match mode {
        FunMode::Linear => {
            if uses.len() != 1 {
                return Err(TranslateError::LinearParamNotUsedOnce {
                    param: param.to_string(),
                    uses: uses.len(),
                });
            }
            let tag = Tag {
                raw: RawTag::TFun,
                sub: SubTag::Arg,
                polarity: Polarity::Constructor,
            };
            graph.add_edge(uses[0], fun_nid, tag);
        }
        FunMode::WithDup => {
            let dup_nid = graph.alloc_vertex();
            let tag = Tag {
                raw: RawTag::TFun,
                sub: SubTag::Arg,
                polarity: Polarity::Constructor,
            };
            graph.add_edge(dup_nid, fun_nid, tag);
            for (i, use_v) in uses.into_iter().enumerate() {
                let tag = Tag {
                    raw: RawTag::TDup(param.to_string()),
                    sub: SubTag::DupI(i),
                    polarity: Polarity::Destructor,
                };
                graph.add_edge(use_v, dup_nid, tag);
            }
        }
    }
    Ok(())
}

fn translate(
    expr: &Expr,
    graph: &mut Graph<Tag>,
) -> Result<(VertexId, TranslateEnv), TranslateError> {
    match expr {
        Expr::Var(v) => {
            let nid = graph.alloc_vertex();
            let mut env = HashMap::new();
            env.insert(VarName(v.0.clone()), vec![nid]);
            Ok((nid, env))
        }
        Expr::Lam { mode, param, body } => {
            let Pat::Var(param_var) = param else {
                return Err(TranslateError::ExpectedVarPattern);
            };
            let (body_nid, mut body_env) = translate(body, graph)?;
            let fun_nid = graph.alloc_vertex();
            let uses = env_remove(&mut body_env, &VarName(param_var.0.clone()));
            let tag = Tag {
                raw: RawTag::TFun,
                sub: SubTag::Ret,
                polarity: Polarity::Constructor,
            };
            graph.add_edge(body_nid, fun_nid, tag);
            connect_param(graph, fun_nid, &param_var.0, uses, *mode)?;
            Ok((fun_nid, body_env))
        }
        Expr::App { head, spine } => {
            let (mut curr_nid, mut env) = translate(head, graph)?;
            for arg in spine {
                let (arg_nid, arg_env) = translate(arg, graph)?;
                let app_nid = graph.alloc_vertex();
                let arg_tag = Tag {
                    raw: RawTag::TFun,
                    sub: SubTag::Arg,
                    polarity: Polarity::Destructor,
                };
                let ret_tag = Tag {
                    raw: RawTag::TFun,
                    sub: SubTag::Ret,
                    polarity: Polarity::Destructor,
                };
                graph.add_edge(arg_nid, curr_nid, arg_tag);
                graph.add_edge(app_nid, curr_nid, ret_tag);
                env = merge_env(env, arg_env);
                curr_nid = app_nid;
            }
            Ok((curr_nid, env))
        }
        Expr::Tuple(elems) => {
            let tuple_nid = graph.alloc_vertex();
            let mut env = HashMap::new();
            for (i, elem) in elems.iter().enumerate() {
                let (elem_nid, elem_env) = translate(elem, graph)?;
                let tag = Tag {
                    raw: RawTag::TPair,
                    sub: SubTag::TupI(i),
                    polarity: Polarity::Constructor,
                };
                graph.add_edge(elem_nid, tuple_nid, tag);
                env = merge_env(env, elem_env);
            }
            Ok((tuple_nid, env))
        }
        Expr::Int(_) | Expr::Plus => {
            let nid = graph.alloc_vertex();
            Ok((nid, HashMap::new()))
        }
    }
}

pub fn run_translate(expr: &Expr) -> Result<SharingGraph, TranslateError> {
    let mut graph = Graph::new();
    let (root, env) = translate(expr, &mut graph)?;
    Ok(SharingGraph {
        graph,
        root,
        free_vars: env,
    })
}
