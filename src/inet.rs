use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct NodeId(usize);

/// A port connection: (Tag, target NodeId)
/// The Tag is stored on the port/edge, not derived from the node.
pub type Port = (Tag, NodeId);

#[derive(Clone, Debug)]
pub struct Node {
    pub ports: Vec<Port>, // outgoing connections with their tags
}

#[derive(Clone, Debug)]
pub struct Graph {
    nodes: Vec<Option<Node>>, // indexed by NodeId, None = deleted
}

impl Graph {
    pub fn new() -> Self {
        Graph { nodes: Vec::new() }
    }

    pub fn alloc(&mut self, node: Node) -> NodeId {
        let id = NodeId(self.nodes.len());
        self.nodes.push(Some(node));
        id
    }

    pub fn alloc_empty(&mut self) -> NodeId {
        self.alloc(Node { ports: Vec::new() })
    }

    pub fn get(&self, id: NodeId) -> Option<&Node> {
        self.nodes.get(id.0).and_then(|n| n.as_ref())
    }

    pub fn get_mut(&mut self, id: NodeId) -> Option<&mut Node> {
        self.nodes.get_mut(id.0).and_then(|n| n.as_mut())
    }

    pub fn add_port(&mut self, from: NodeId, tag: Tag, to: NodeId) {
        if let Some(node) = self.get_mut(from) {
            node.ports.push((tag, to));
        }
    }

    pub fn get_outgoing(&self, id: NodeId) -> Vec<(Tag, NodeId)> {
        self.get(id)
            .map(|node| node.ports.clone())
            .unwrap_or_default()
    }

    pub fn get_incoming(&self, id: NodeId) -> Vec<(NodeId, Tag)> {
        let mut incoming = Vec::new();
        for (i, node_opt) in self.nodes.iter().enumerate() {
            if let Some(node) = node_opt {
                for (tag, target) in &node.ports {
                    if *target == id {
                        incoming.push((NodeId(i), tag.clone()));
                    }
                }
            }
        }
        incoming
    }

    pub fn remove_node(&mut self, id: NodeId) {
        if let Some(slot) = self.nodes.get_mut(id.0) {
            *slot = None;
        }
        for node_opt in &mut self.nodes {
            if let Some(node) = node_opt {
                node.ports.retain(|(_, target)| *target != id);
            }
        }
    }

    pub fn merge_nodes(&mut self, old: NodeId, new: NodeId) {
        for node_opt in &mut self.nodes {
            if let Some(node) = node_opt {
                for (_, target) in &mut node.ports {
                    if *target == old {
                        *target = new;
                    }
                }
            }
        }
    }

    pub fn alloc_with_ports(&mut self, p1: (Tag, NodeId), p2: (Tag, NodeId)) -> NodeId {
        self.alloc(Node {
            ports: vec![p1, p2],
        })
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
    pub graph: Graph,
    pub root: NodeId,
    pub free_vars: HashMap<VarName, Vec<NodeId>>,
}

pub type Remap = Vec<(NodeId, NodeId)>;

fn apply_remap(remap: &Remap, v: NodeId) -> NodeId {
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
    pub fn merge_nodes(&mut self, old: NodeId, new: NodeId) {
        self.graph.merge_nodes(old, new);
        if self.root == old {
            self.root = new;
        }
        for nodes in self.free_vars.values_mut() {
            for v in nodes.iter_mut() {
                if *v == old {
                    *v = new;
                }
            }
        }
    }

    pub fn protected_nodes(&self) -> Vec<NodeId> {
        let mut protected = vec![self.root];
        for nodes in self.free_vars.values() {
            protected.extend(nodes);
        }
        protected
    }

    pub fn eliminate_cut(&mut self, v: NodeId) -> Result<Remap, INetError> {
        let incoming = self.graph.get_incoming(v);
        let pairs = all_pairs(&incoming);
        self.graph.remove_node(v);

        let mut remap: Remap = Vec::new();
        for ((v1, t1), (v2, t2)) in pairs {
            let v1 = apply_remap(&remap, v1);
            let v2 = apply_remap(&remap, v2);
            match t1.relation(&t2) {
                Interaction::Ignore => {}
                Interaction::Annihilate => {
                    self.merge_nodes(v2, v1);
                    remap.push((v2, v1));
                }
                Interaction::Commute => {
                    self.graph.alloc_with_ports((t2, v1), (t1, v2));
                }
                Interaction::Stuck => return Err(INetError::Stuck(t1, t2)),
            }
        }
        Ok(remap)
    }

    pub fn eval(
        &mut self,
        protected: &mut Vec<NodeId>,
        curr: NodeId,
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
        let mut protected = self.protected_nodes();
        let root = self.root;
        self.eval(&mut protected, root, 10000)?;
        Ok(())
    }

    pub fn nf(&mut self) -> Result<(), INetError> {
        self.whnf()?;
        let incoming: Vec<NodeId> = self
            .graph
            .get_incoming(self.root)
            .into_iter()
            .map(|(v, _)| v)
            .collect();
        let mut protected = self.protected_nodes();
        protected.extend(&incoming);

        for v in incoming {
            self.eval(&mut protected, v, 10000)?;
        }
        Ok(())
    }
}

// Translation from Expr to SharingGraph

use crate::expr::{Expr, FunMode, Pat};

type TranslateEnv = HashMap<VarName, Vec<NodeId>>;

fn env_remove(env: &mut TranslateEnv, param: &VarName) -> Vec<NodeId> {
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
    graph: &mut Graph,
    fun_nid: NodeId,
    param: &str,
    uses: Vec<NodeId>,
    mode: FunMode,
) -> Result<(), TranslateError> {
    let arg_tag = Tag {
        raw: RawTag::TFun,
        sub: SubTag::Arg,
        polarity: Polarity::Constructor,
    };
    match mode {
        FunMode::Linear => {
            if uses.len() != 1 {
                return Err(TranslateError::LinearParamNotUsedOnce {
                    param: param.to_string(),
                    uses: uses.len(),
                });
            }
            graph.add_port(uses[0], arg_tag, fun_nid);
        }
        FunMode::WithDup => {
            let dup_nid = graph.alloc(Node {
                ports: vec![(arg_tag, fun_nid)],
            });
            for (i, use_v) in uses.into_iter().enumerate() {
                let dup_tag = Tag {
                    raw: RawTag::TDup(param.to_string()),
                    sub: SubTag::DupI(i),
                    polarity: Polarity::Destructor,
                };
                graph.add_port(use_v, dup_tag, dup_nid);
            }
        }
    }
    Ok(())
}

fn translate(
    expr: &Expr,
    graph: &mut Graph,
) -> Result<(NodeId, TranslateEnv), TranslateError> {
    match expr {
        Expr::Var(v) => {
            let nid = graph.alloc_empty();
            let mut env = HashMap::new();
            env.insert(VarName(v.0.clone()), vec![nid]);
            Ok((nid, env))
        }
        Expr::Lam { mode, param, body } => {
            let Pat::Var(param_var) = param else {
                return Err(TranslateError::ExpectedVarPattern);
            };
            let (body_nid, mut body_env) = translate(body, graph)?;
            let uses = env_remove(&mut body_env, &VarName(param_var.0.clone()));
            let fun_nid = graph.alloc_empty();
            let ret_tag = Tag {
                raw: RawTag::TFun,
                sub: SubTag::Ret,
                polarity: Polarity::Constructor,
            };
            graph.add_port(body_nid, ret_tag, fun_nid);
            connect_param(graph, fun_nid, &param_var.0, uses, *mode)?;
            Ok((fun_nid, body_env))
        }
        Expr::App { head, spine } => {
            let (mut curr_nid, mut env) = translate(head, graph)?;
            for arg in spine {
                let (arg_nid, arg_env) = translate(arg, graph)?;
                let ret_tag = Tag {
                    raw: RawTag::TFun,
                    sub: SubTag::Ret,
                    polarity: Polarity::Destructor,
                };
                let arg_tag = Tag {
                    raw: RawTag::TFun,
                    sub: SubTag::Arg,
                    polarity: Polarity::Destructor,
                };
                let app_nid = graph.alloc(Node {
                    ports: vec![(ret_tag, curr_nid)],
                });
                graph.add_port(arg_nid, arg_tag, curr_nid);
                env = merge_env(env, arg_env);
                curr_nid = app_nid;
            }
            Ok((curr_nid, env))
        }
        Expr::Tuple(elems) => {
            let tuple_nid = graph.alloc_empty();
            let mut env = HashMap::new();
            for (i, elem) in elems.iter().enumerate() {
                let (elem_nid, elem_env) = translate(elem, graph)?;
                let tup_tag = Tag {
                    raw: RawTag::TPair,
                    sub: SubTag::TupI(i),
                    polarity: Polarity::Constructor,
                };
                graph.add_port(elem_nid, tup_tag, tuple_nid);
                env = merge_env(env, elem_env);
            }
            Ok((tuple_nid, env))
        }
        Expr::Int(_) | Expr::Plus => {
            let nid = graph.alloc_empty();
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
