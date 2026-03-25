# 💻 OCaml Bytecode Virtual Machine

## 📖 Project Overview
This project is a functional **Virtual Machine (VM)** built in C, designed to bridge the gap between high-level functional logic and low-level hardware execution. It interprets a specific bytecode format (`.sobf`) by simulating a CPU with a **stack-based architecture** and a dedicated **accumulator**.

The goal was to replicate the core execution mechanics of a language like OCaml, focusing on memory efficiency and fast instruction dispatching.

---

## ⚙️ How it Works (Core Logic)

### 1. The Stack & Accumulator Model
Unlike pure stack machines, this VM uses an **Accumulator (acc)**. 
- Most operations take the `acc` as the first operand and the top of the `stack` as the second. 
- This reduces stack traffic and speeds up the execution of nested functional expressions.

### 2. Low-Level Data Representation (LSB Tagging)
To handle types without a heavy metadata system, I implemented **Least Significant Bit (LSB) Tagging**:
- **Integers:** Stored as `(n << 1) | 1`. This allows the VM to identify a 31-bit integer instantly.
- **Pointers/Blocks:** Stored with a `0` tag at the end, pointing to memory addresses.
*This mimics how the real OCaml runtime optimizes memory and distinguishes integers from heap pointers.*

### 3. Fetch-Decode-Execute Loop
The VM reads binary instructions from a program counter (PC), decodes the opcode, and dispatches it to the corresponding C function. It handles:
- **Arithmetic:** `ADD`, `SUB`, `MUL`, `DIV`, etc.
- **Control Flow:** Conditional (`BRANCHIF`) and unconditional (`BRANCH`) jumps.
- **Context Management:** `PUSH`, `POP`, and `ACC` for stack frame manipulation.


## 🛠 Technologies & Tools
- **Language:** C (Standard ISO/IEC 9899).
- **Tooling:** GCC for compilation, GDB for low-level debugging.
- **Architecture:** Stack + Accumulator VM.

## 🧠 What I Learned 

Building this VM was a deep dive into the "black box" of programming languages. It taught me:
- **Memory Integrity:** Handling raw pointers and bitwise operations requires extreme rigor to avoid segmentation faults.
- **The "High-to-Low" Bridge:** I now  understand how a recursive function (like `fact.sobf`) is translated into a series of jumps and stack manipulations at the CPU level.
- **Binary Parsing:** I learned how to read and interpret custom binary file formats, ensuring the machine correctly reconstructs instructions from raw bytes.
- **Debugging Complexity:** Debugging a VM is unique—you aren't just debugging your C code, you're debugging the logic of the program *running inside* your VM.

---

## 🧪 Validated Use Cases
The machine has been stress-tested with several complex bytecode files:
- **`fact.sobf`**: Successfully handles recursive-style loops and arithmetic.
- **`wumpus.sobf` & `pinetree.sobf`**: Validates the VM's ability to handle large instruction sets and complex branching logic without memory leaks.

---

## 🚀 Looking Forward
- **Garbage Collection:** The next step is implementing a Mark-and-Sweep GC to manage the heap automatically.
- **Performance:** Exploring `computed gotos` (a GCC extension) to replace the `switch` statement for faster instruction dispatching.
