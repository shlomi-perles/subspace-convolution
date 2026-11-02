// Shared benchmark utilities: timing protocol, CSV output, environment capture.
#pragma once

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <map>
#include <sstream>
#include <string>
#include <vector>

#include <sys/resource.h>
#include <unistd.h>

namespace bench {

using clk = std::chrono::steady_clock;

inline double seconds_since(clk::time_point t0) {
  return std::chrono::duration<double>(clk::now() - t0).count();
}

struct Timing {
  double median = 0, min = 0, max = 0;
  int reps = 0;
};

// One untimed warm-up, then `reps` timed runs.  `prepare` runs before each
// timed call and is excluded from the measurement (e.g. restoring the input).
inline Timing time_runs(int reps, const std::function<void()>& prepare, const std::function<void()>& body,
                        bool warmup = true) {
  if (warmup) {
    prepare();
    body();
  }
  std::vector<double> ts;
  for (int r = 0; r < reps; ++r) {
    prepare();
    auto t0 = clk::now();
    body();
    ts.push_back(seconds_since(t0));
  }
  std::sort(ts.begin(), ts.end());
  Timing t;
  t.reps = reps;
  t.min = ts.front();
  t.max = ts.back();
  t.median = ts[ts.size() / 2];
  return t;
}

// Adaptive repetition count: aim for ~`budget` seconds per measurement.
inline int reps_for(double single_run_s, double budget = 3.0, int lo = 3, int hi = 25) {
  if (single_run_s <= 0) return hi;
  int r = int(budget / single_run_s);
  return std::max(lo, std::min(hi, r));
}

inline double peak_rss_gb() {
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
  return ru.ru_maxrss / 1048576.0;  // KiB -> GiB
}

class Csv {
 public:
  Csv(const std::string& path, const std::vector<std::string>& cols) : cols_(cols) {
    bool exists = std::ifstream(path).good();
    out_.open(path, std::ios::app);
    if (!exists) {
      for (size_t i = 0; i < cols.size(); ++i) out_ << (i ? "," : "") << cols[i];
      out_ << "\n";
    }
  }
  void row(const std::map<std::string, std::string>& kv) {
    for (size_t i = 0; i < cols_.size(); ++i) {
      auto it = kv.find(cols_[i]);
      out_ << (i ? "," : "") << (it == kv.end() ? "" : quote(it->second));
    }
    out_ << "\n";
    out_.flush();
  }

 private:
  static std::string quote(const std::string& v) {  // RFC 4180 quoting when needed
    if (v.find_first_of(",\"\n") == std::string::npos) return v;
    std::string q = "\"";
    for (char ch : v) q += (ch == '"') ? std::string("\"\"") : std::string(1, ch);
    return q + "\"";
  }
  std::vector<std::string> cols_;
  std::ofstream out_;
};

template <class T>
inline std::string str(T v) {
  std::ostringstream os;
  os.precision(10);
  os << v;
  return os.str();
}

inline std::string arg(int argc, char** argv, const std::string& key, const std::string& def) {
  for (int i = 1; i + 1 < argc; ++i)
    if (argv[i] == "--" + key) return argv[i + 1];
  return def;
}

}  // namespace bench
