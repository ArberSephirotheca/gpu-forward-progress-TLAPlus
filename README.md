# gpu-forward-progress-TLAPlus

## Pre-requisites
- [Docker](https://docs.docker.com/install/) or [Podman](https://github.com/containers/podman/blob/main/docs/tutorials/podman_tutorial.md)
- [Git](https://git-scm.com/book/en/v2/Getting-Started-Installing-Git)
- [Earthly](https://earthly.dev/get-earthly)

## Get Started
Make sure you've started the docker service
```bash
systemctl service docker start
```
And run earthly bootstrap (this step is only necessary the first time)
```bash
earthly bootstrap
```
Then, run following to see the output
```bash
earthly +tlaplus-image --INPUT=<glsl compute file> --OUT=<format> --SG_SIZE=<size of subgroup> --WG_SIZE=<workgroup size> --NUM_WG=<number of workgroup> --SCH=<scheduler>
```

## Example:
`earthly -i +tlaplus-image --INPUT example_shader_program/producer_consumer.comp --OUT=all --SG_SIZE=1 --WG_SIZE=1 --NUM_WG=2 --SCH=HSA`

## Command Line Option
- *format*: text, dot, all
- *scheduler*: HSA, OBE

## List of supported SPIR-V Instructions
- OpVariable,
- OpReturn,
- OpLoad,
- OpStore,
- OpAtomicLoad,
- OPAtomicStore,
- OpBranch,
- OpBranchConditional,
- OpLabel,
- OpSelectionMerge,
- OpLoopMerge,
- OpAtomicExchange,
- OpEqual,
- OpNotEqual,
- OpLess,
- OpLessOrEqual,
- OpGreater,
- GreaterOrEqual,
- OpAdd,
- OpSub,
- OpMul,

**Note**: The model treats the following instructions as equivalent:
- `OpLoad` and `OpAtomicLoad`
- `OpStore` and `OpAtomicStore`

## Supported Type
- int
- uint
- bool

## Memory Semantics
The model does not implement any extension to memory semantics, and all SPIR-V instructions
are behaving like `SequentiallyConsistent`.
