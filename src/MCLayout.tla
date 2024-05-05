---- MODULE MCLayout ----
LOCAL INSTANCE Integers
(* Layout Configuration *)
SubgroupSize == 2
WorkGroupSize == 2
NumWorkGroups == 2
NumThreads == WorkGroupSize * NumWorkGroups

LOCAL INSTANCE Layout

GlobalInvocationId(tid) == tid-1

LocalInvocationId(tid) == GlobalInvocationId(tid) % WorkGroupSize

WorkGroupId(tid) == GlobalInvocationId(tid) \div WorkGroupSize
    
SubgroupId(tid) == LocalInvocationId(tid) \div SubgroupSize

SubgroupInovcationId(tid) == LocalInvocationId(tid) % SubgroupSize

(* Thread Layout *)

====