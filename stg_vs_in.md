- STG keeps args on the stack
- STG keeps closure as assembly, IN uses HeapPtr graph


IN copies the closure and physically connects the pointer hole that was connected to lambda to the existing pointer.
The middle ground would be ...
When we connect, we go through indirection which is a return address.

so when we are called, we are pushing ret address on the stack, when we access the variable we are using the ret address to look up appropriate env
so the env of the closure is a map  ([ret address] -> env)
in stg instead we don't have a single global env map, we have multiple distributed envs
