const char *__asan_default_options(void) {
    return "detect_leaks=0:abort_on_error=1:disable_coredump=0";
}
