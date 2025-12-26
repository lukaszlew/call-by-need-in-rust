linear.md
An explicit substitution calculus for ILL, adopting the Benton-Bierman-de Paiva-Hyland promotion syntax and the Kesner-Lengrand structural explicit substitutions ($\lambda_{lxr}$), treating contraction and weakening as structural operations on the exponential modality ($!$).

1. Syntax
Let $x, y, z$ denote variables. The set of terms $\Lambda_{!}$ is defined by:
$$\begin{aligned} t, u ::= \;& x & (\text{Variable}) \\ \mid \;& \lambda x. t & (\text{Abstraction}) \\ \mid \;& t \, u & (\text{Application}) \\ \mid \;& ![\vec{x} = \vec{u} \mid t] & (\text{Promoted Box}) \\ \mid \;& \text{let } !x = t \text{ in } u & (\text{Dereliction}) \\ \mid \;& \text{let } [y_1, \dots, y_n] = t \text{ in } u & (\text{Structural: Weakening/Contraction}) \end{aligned}$$
Notation:
$\vec{x} = \vec{u}$ abbreviates the explicit capture list $x_1 = u_1, \dots, x_k = u_k$.
In the term $![\vec{x} = \vec{u} \mid t]$, the term $t$ is the box body, $\vec{u}$ are the captured resources, and $\vec{x}$ are variables bound in $t$ (renaming $\vec{u}$).
2. Structural Constraints
Strict Linearity: Every variable in the typing context $\Delta$ must appear exactly once in the term.
Box Closure: In $![\vec{x} = \vec{u} \mid t]$, the body $t$ must be closed, except for the free variables in $\vec{x}$. All free variables of the entire term must appear in $\vec{u}$.
Bang Typing: In let [...] = t and let !x = t, the term $t$ must have type $!A$.
3. Typing Rules
Judgment: $\Delta \vdash t : A$.
Logical Rules
$$\frac{\Delta, x:A \vdash t : B}{\Delta \vdash \lambda x. t : A \multimap B} (\multimap_I) \quad \frac{\Delta_1 \vdash t : A \multimap B \quad \Delta_2 \vdash u : A}{\Delta_1, \Delta_2 \vdash t \, u : B} (\multimap_E)$$
Exponential Rules
Promotion (Box Introduction)
Requires explicit capture of all dependencies $\vec{u}$, which must themselves be of exponential type.
$$\frac{\Delta_1 \vdash u_1 : !A_1 \dots \Delta_k \vdash u_k : !A_k \quad \quad x_1:!A_1, \dots, x_k:!A_k \vdash t : B}{\Delta_1, \dots, \Delta_k \vdash ![\vec{x} = \vec{u} \mid t] \, : \, !B}$$
Dereliction (Box Elimination)
Extracts the linear content from the exponential.
$$\frac{\Delta_1 \vdash t : !A \quad \quad \Delta_2, x:A \vdash u : C}{\Delta_1, \Delta_2 \vdash \text{let } !x = t \text{ in } u : C}$$
Structural Control (Unified Weakening/Contraction)
Splits the "wire" of a generic exponential resource $!A$ into $n$ handles.
$$\frac{\Delta_1 \vdash t : !A \quad \quad \Delta_2, y_1:!A, \dots, y_n:!A \vdash s : C}{\Delta_1, \Delta_2 \vdash \text{let } [y_1, \dots, y_n] = t \text{ in } s : C}$$
If $n=0$: Weakening (Discard).
If $n=1$: Identity (Wire extension).
If $n \geq 2$: Contraction (Copy).

4. Reduction Rules
$\beta$-Reduction
$$(\lambda x. t) \, u \longrightarrow t[u/x]$$
Principal Cut (Dereliction on Box)
Opening a box triggers the substitution of captured resources into the body.
$$\text{let } !y = ![\vec{x} = \vec{u} \mid t] \text{ in } s \longrightarrow s [ t [\vec{u} / \vec{x}] / y ]$$
Structural Cut (Management on Box)
Applying a structural operation to a constructed box pushes the operation to the captured resources. The box $t$ is duplicated (or discarded), and the resources $\vec{u}$ are structurally split to satisfy the new dependencies.
$$\text{let } [y_1, \dots, y_n] = ![\vec{x} = \vec{u} \mid t] \text{ in } s$$
$$\downarrow$$
$$\text{let } [\vec{u}^1, \dots, \vec{u}^n] = \vec{u} \text{ in } s \left[ \frac{![\vec{x} = \vec{u}^1 \mid t]}{y_1}, \dots, \frac{![\vec{x} = \vec{u}^n \mid t]}{y_n} \right]$$
Note: $\text{let } [\dots] = \vec{u}$ implies a vectorized structural let, splitting each resource $u_i$ into $n$ copies $(u_i^1 \dots u_i^n)$.

5. Exercises
Exercise 1: The Vacuous Capture
Task: Construct a term of type $!A \multimap !(!A \multimap !A)$ that takes a resource $x:!A$, discards it, and returns a box containing the identity function.
Hint: You must use the unified structural rule with $n=0$ to handle $x$, but the box itself must capture nothing.
<details>
<summary><b>Solution</b></summary>
$$\lambda x. \text{let } [] = x \text{ in } ![\emptyset = \emptyset \mid \lambda y. ![\emptyset = \emptyset \mid y]]$$
Note: The inner identity requires its own box structure if the return type is $!(!A \multimap !A)$. If the return type is just $!(!A \multimap A)$, the inner term is simpler.
</details>
Exercise 2: Deep Copy
Task: Reduce the term $\text{let } [a, b] = ![k=u \mid k] \text{ in } (a, b)$.
Assume $u$ is a variable of type $!A$.
Hint: This is a direct application of the Structural Cut rule with $n=2$.
<details>
<summary><b>Solution</b></summary>
Identify captured resource: $u$.
Apply Structural Cut: Split $u$ into $u^1, u^2$.
Result:
$$\text{let } [u^1, u^2] = u \text{ in } (![k=u^1 \mid k], ![k=u^2 \mid k])$$
</details>
Exercise 3: The Deadlock (Type checking)
Task: Explain why the following term is ill-typed:
$$\lambda x. ![y=x \mid \text{let } !z = y \text{ in } z]$$
Assume $x$ has type $A$ (linear).
<details>
<summary><b>Solution</b></summary>
The capture syntax $![y=x \dots]$ requires that the captured resource $x$ be of type $!T$ (Exponential). Here, $x$ is type $A$ (Linear). You cannot promote a linear variable directly; it must be a box to survive the closure constraint.
</details>

Design Justification: let [...] vs let ![...]
I selected the syntax let [x_1, \dots, x_n] = t without the bang for the structural rule.
Reasoning:
Type Preservation: This operation maps $!A \to (!A)^n$. It operates entirely within the exponential layer. The variables $x_i$ bound by this construct are still of type $!A$.
Semantics of !: In Linear Logic syntax, the pattern !x (or let !x) usually signifies a boundary crossing (Dereliction: $!A \to A$) or a pattern match on the constructor.
Clarity: Using let ![...] would visually conflate "Opening the box" (Dereliction) with "Copying the box" (Contraction). By omitting the bang, we clarify that we are manipulating the handle to the resource, not the resource itself.
