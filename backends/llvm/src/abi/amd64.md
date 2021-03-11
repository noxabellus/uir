# AMD64 C ABI
[Source](https://web.archive.org/web/20160801075146/http://www.x86-64.org/documentation/abi.pdf)


## Definitions

We first define a number of classes to classify arguments. The
classes are corresponding to AMD64 register classes and defined as:

- `Integer`
	> This class consists of integral types that fit into one of the general purpose registers.

- `Ssse`
	> The class consists of types that fit into a vector register.

- `SseUp`
	> The class consists of types that fit into a vector register and can be passed and returned in the upper bytes of it.

- ``X87``
	> These classes consists of types that fit in a x87 FPU register.

- `X87Up`
	> These classes consists of types that fit in a x87 FPU register and can be passed and returned in the upper bytes of it.

- `ComplexX87`
	> This class consists of types that will be returned via the x87 FPU.

- `NoClass`
	> This class is used as initializer in the algorithms. It will be used for padding and empty structures and unions.

- `Memory`
	> This class consists of types that will be passed and returned in memory via the stack.


## Classification

The size of each argument gets rounded up to *eightbytes*.

The basic types are assigned their natural classes:

- Arguments of c types (signed and unsigned) `_Bool`, `char`, `short`, `int`, `long`, `long long`, and pointers are in the `Integer` class.

- Arguments of c types `float`, `double`, `_Decimal32`, `_Decimal64` and `__m64` are in class `Sse`.

- Arguments of c types `__float128`, `_Decimal128` and `__m128` are split into two halves. The least significant ones belong to class `Sse`, the most significant one to class `SseUp`.

- Arguments of type `__m256` are split into four *eightbyte* chunks. The least significant one belongs to class `Sse` and all the others to class `SseUp`.

- The 64-bit mantissa of arguments of type `long double` belongs to class ``X87``, the 16-bit exponent plus 6 bytes of padding belongs to class `X87Up`.

- Arguments of type `i128` offer the same operations as `Integer`s, yet they do not fit into one general purpose register but require two registers.
> For classification purposes `i128` is treated as if it were implemented as `struct i128 (i64, i64)` with the exception that arguments of type `i128` that are stored in memory must be aligned on a 16-byte boundary.

- Arguments of c types `complex T` where `T` is one of the types `float` or `double`
  are treated as if they are implemented as:`struct complex<T> (T, T)`

- A variable of c type `complex long double` is classified as type `ComplexX87`.


The classification of aggregate (structures and arrays) and union types works
as follows:

1. If the size of an object is larger than four *eightbytes*, or it contains unaligned
fields, it has class `Memory`.
> The post merger clean up described later ensures that, for the processors that do not support
> the `__m256` type, if the size of an object is larger than two *eightbytes* and the first *eightbyte* is not
> `Sse` or any other *eightbyte* is not `SseUp`, it still has class `Memory`. This in turn ensures that for
> processors that do support the `__m256` type, if the size of an object is four *eightbytes* and the first
> *eightbyte* is `Sse` and all other *eightbytes* are `SseUp`, it can be passed in a register.

2. If a C++ object has either a non-trivial copy constructor or a non-trivial
destructor, it is passed by invisible reference (the object is replaced in the
parameter list by a pointer that has class `Integer`).
> A de/constructor is trivial if it is an implicitly-declared default de/constructor and if:
> - its class has no virtual functions and no virtual base classes, and
> - all the direct base classes of its class have trivial de/constructors, and
> - for all the nonstatic data members of its class that are of class type (or array thereof), each such class has a trivial de/constructor.

> An object with either a non-trivial copy constructor or a non-trivial destructor cannot be passed by value because such objects must have well defined addresses. Similar issues apply when returning an object from a function.

3. If the size of the aggregate exceeds a single *eightbyte*, each is classified
separately. Each *eightbyte* gets initialized to class `NoClass`.

4. Each field of an object is classified recursively so that always two fields are
considered. The resulting class is calculated according to the classes of the
fields in the *eightbyte*:
	- If both classes are equal, this is the resulting class.
	- If one of the classes is `NoClass`, the resulting class is the other class.
	- If one of the classes is `Memory`, the result is the `Memory` class.
	- If one of the classes is `Integer`, the result is the `Integer`.
	- If one of the classes is `X87`, `X87Up`, `ComplexX87` class, `Memory` is used as class.
	- Otherwise class `Sse` is used.

5. Then a post merger cleanup is done:
	- If one of the classes is `Memory`, the whole argument is passed in memory.
	- If `X87Up` is not preceded by `X87`, the whole argument is passed in memory.
	- If the size of the aggregate exceeds two *eightbytes* and the first *eightbyte* isn’t `Sse` or any other *eightbyte* isn’t `SseUp`, the whole argument is passed in memory.
	- If `SseUp` is not preceded by `Sse` or `SseUp`, it is converted to `Sse`.



## Passing

Once arguments are classified, the registers get assigned
(in left-to-right order) for passing as follows:

1. If the class is `Memory`, pass the argument on the stack.
2. If the class is `Integer`, the next available register of the sequence `%rdi`, `%rsi`, `%rdx`, `%rcx`, `%r8` and `%r9` is used13.
	> Note that `%r11` is neither required to be preserved, nor is it used to pass arguments. Making this register available as scratch register means that code in the PLT need not spill any registers when computing the address to which control needs to be transferred. `%rax` is used to indicate the number of vector arguments passed to a function requiring a variable number of arguments. `%r10`  is used for passing a function’s static chain pointer.

3. If the class is `Sse`, the next available vector register is used, the registers are taken in the order from `%xmm0` to `%xmm7`.
4. If the class is `SseUp`, the *eightbyte* is passed in the next available *eightbyte* chunk of the last used vector register.
5. If the class is `X87`, `X87Up` or `ComplexX87`, it is passed in memory.

When a value of c type `_Bool` is returned or passed in a register or on the stack,
bit 0 contains the truth value and bits 1 to 7 shall be zero.
> Other bits are left unspecified, hence the consumer side of those values can rely on it being 0 or 1 when truncated to 8 bit.

If there are no registers available for any *eightbyte* of an argument, the whole
argument is passed on the stack.

If registers have already been assigned for some
*eightbytes* of such an argument, the assignments get reverted.

Once registers are assigned, the arguments passed in memory are pushed on
the stack in reversed (right-to-left) order.
> Right-to-left order on the stack makes the handling of functions that take a variable number of arguments simpler. The location of the first argument can always be computed statically, based on the type of that argument. It would be difficult to compute the address of the first argument if the arguments were pushed in left-to-right order.

For calls that may call functions that use varargs or stdargs (prototype-less
calls or calls to functions containing ellipsis (. . . ) in the declaration) `%al` is used
as hidden argument to specify the number of vector registers used.
> Note that the rest of `%rax` is undefined, only the contents of `%al` is defined. The contents of `%al` do not need to match exactly the number of registers, but must be an upper bound on the number of vector registers used and is in the range 0–8 inclusive.

When passing `__m256` arguments to functions that use varargs or stdarg,
function prototypes must be provided. Otherwise, the run-time behavior is undefined.




## Returning of Values

The returning of values is done according to the following
algorithm:

1. Classify the return type with the classification algorithm.
2. If the type has class `Memory`, then the caller provides space for the return value and passes the address of this storage in `%rdi` as if it were the first argument to the function. In effect, this address becomes a “hidden” first argument. This storage must not overlap any data visible to the callee through other names than this argument. On return `%rax` will contain the address that has been passed in by the caller in `%rdi`.
3. If the class is `Integer`, the next available register of the sequence `%rax`, `%rdx` is  used.
4. If the class is `Sse`, the next available vector register of the sequence `%xmm0`, `%xmm1` is used.
5. If the class is `SseUp`, the *eightbyte* is returned in the next available *eightbyte* chunk of the last used vector register.
6. If the class is `X87`, the value is returned on the `X87` stack in `%st0` as 80-bit x87 number.
7. If the class is `X87Up`, the value is returned together with the previous `X87` value in `%st0`.
8. If the class is `ComplexX87`, the real part of the value is returned in `%st0` and the imaginary part in `%st1`.