// std::vector allocator that requests transparent huge pages for large buffers.
// Random access over tables of 10^7+ entries is TLB-bound with 4 KiB pages; all
// methods in the benchmarks (fast, hybrid, lattice, direct) use this allocator
// for their data and index arrays so that the comparison is not skewed.
#pragma once

#include <cstdlib>
#include <new>
#include <vector>

#include <sys/mman.h>

namespace fsc {

template <class T>
struct HugeAlloc {
  using value_type = T;
  HugeAlloc() = default;
  template <class U>
  HugeAlloc(const HugeAlloc<U>&) {}
  T* allocate(std::size_t n) {
    std::size_t bytes = n * sizeof(T);
    constexpr std::size_t kHuge = std::size_t(2) << 20;
    if (bytes >= kHuge) {
      std::size_t rounded = (bytes + kHuge - 1) / kHuge * kHuge;
      void* p = std::aligned_alloc(kHuge, rounded);
      if (!p) throw std::bad_alloc();
#ifdef MADV_HUGEPAGE
      madvise(p, rounded, MADV_HUGEPAGE);
#endif
      return static_cast<T*>(p);
    }
    void* p = std::malloc(bytes ? bytes : 1);
    if (!p) throw std::bad_alloc();
    return static_cast<T*>(p);
  }
  void deallocate(T* p, std::size_t) { std::free(p); }
  template <class U>
  bool operator==(const HugeAlloc<U>&) const { return true; }
  template <class U>
  bool operator!=(const HugeAlloc<U>&) const { return false; }
};

template <class T>
using hvec = std::vector<T, HugeAlloc<T>>;

}  // namespace fsc
