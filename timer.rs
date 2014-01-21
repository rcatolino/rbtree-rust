extern mod extra;

use extra::time;
use std::cmp::{min, max};

pub struct Stats {
  times_called: u64,
  min: u64,
  max: u64,
  cumul: u64,
}

impl Stats {
  // Only used when a print_stats! macro is invoked.
  #[allow(dead_code)]
  pub fn avg(&self) -> u64 {
    if self.times_called != 0 {
      self.cumul/self.times_called
    } else {
      0
    }
  }
}

#[allow(dead_code)]
pub struct Stopwatch {
  priv result_ptr: &'static mut Stats,
  priv start: u64,
}

impl Stopwatch {
  #[allow(dead_code)]
  pub fn new(stats: &'static mut Stats) -> Stopwatch {
    Stopwatch { result_ptr: stats, start: time::precise_time_ns() }
  }
}

impl Drop for Stopwatch {
  fn drop(&mut self) {
    let result = time::precise_time_ns()-self.start;
    self.result_ptr.times_called += 1;
    self.result_ptr.min = min(self.result_ptr.min, result);
    self.result_ptr.max = max(self.result_ptr.max, result);
    self.result_ptr.cumul += result;
  }
}
