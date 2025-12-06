#ifndef BINARYSUB_UTILS_H
#define BINARYSUB_UTILS_H

#include <algorithm>
#include <string>

namespace binarysub {

// Forward declaration for error handling
template <typename E> class unexpected {
public:
  unexpected(E &&error) : error_(std::move(error)) {}
  unexpected(const E &error) : error_(error) {}
  const E &error() const { return error_; }

private:
  E error_;
};

template <typename E> unexpected<E> make_unexpected(E &&error) {
  return unexpected<E>(std::forward<E>(error));
}

template <typename T, typename E> class expected {
public:
  expected() : has_value_(true) {}
  expected(const T &value) : has_value_(true), value_(value) {}

  template <typename U>
  expected(const unexpected<U> &error)
      : has_value_(false), error_(error.error()) {}

  bool has_value() const { return has_value_; }
  operator bool() const { return has_value_; }
  bool operator!() const { return !has_value_; }

  const T &value() const { return value_; }
  T &value() { return value_; }

  const E &error() const { return error_; }

private:
  bool has_value_;
  union {
    T value_;
    E error_;
  };
};

// Specialization for void
template <typename E> class expected<void, E> {
public:
  expected() : has_value_(true) {}

  template <typename U>
  expected(const unexpected<U> &error)
      : has_value_(false), error_(error.error()) {}

  bool has_value() const { return has_value_; }
  operator bool() const { return has_value_; }
  bool operator!() const { return !has_value_; }

  const E &error() const { return error_; }

private:
  bool has_value_;
  E error_;
};

// ======================= Solver cache & error ==============================
struct Error {
  std::string msg;
  static Error make(std::string m);
};
inline Error Error::make(std::string m) { return {std::move(m)}; }

} // namespace binarysub

#endif
