#ifndef BINARYSUB_UTILS_H
#define BINARYSUB_UTILS_H

#include <algorithm>
#include <string>

namespace binarysub {

// Forward declaration for error handling
template <typename E> class unexpected {
public:
  explicit unexpected(const E &error) : error_(error) {}
  explicit unexpected(E &&error) : error_(std::move(error)) {}
  const E &error() const { return error_; }

private:
  E error_;
};

template <typename E> unexpected<typename std::decay<E>::type> make_unexpected(E &&error) {
  return unexpected<typename std::decay<E>::type>(std::forward<E>(error));
}

template <typename T, typename E> class expected {
public:
  expected() : has_value_(true) { new (&value_) T(); }
  expected(const T &value) : has_value_(true) { new (&value_) T(value); }
  expected(T &&value) : has_value_(true) { new (&value_) T(std::move(value)); }

  template <typename U>
  expected(const unexpected<U> &error) : has_value_(false) {
    new (&error_) E(error.error());
  }

  ~expected() {
    if (has_value_) {
      value_.~T();
    } else {
      error_.~E();
    }
  }

  expected(const expected &other) : has_value_(other.has_value_) {
    if (has_value_) {
      new (&value_) T(other.value_);
    } else {
      new (&error_) E(other.error_);
    }
  }

  expected(expected &&other) : has_value_(other.has_value_) {
    if (has_value_) {
      new (&value_) T(std::move(other.value_));
    } else {
      new (&error_) E(std::move(other.error_));
    }
  }

  expected &operator=(const expected &other) {
    if (this != &other) {
      this->~expected();
      has_value_ = other.has_value_;
      if (has_value_) {
        new (&value_) T(other.value_);
      } else {
        new (&error_) E(other.error_);
      }
    }
    return *this;
  }

  expected &operator=(expected &&other) {
    if (this != &other) {
      this->~expected();
      has_value_ = other.has_value_;
      if (has_value_) {
        new (&value_) T(std::move(other.value_));
      } else {
        new (&error_) E(std::move(other.error_));
      }
    }
    return *this;
  }

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
