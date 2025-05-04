import multiprocessing
import time
import traceback

def SetTimeout(func, timeout_sec):
    def wrapper(*args, **kwargs):
        def target_fn(q, *args, **kwargs):
            try:
                result = func(*args, **kwargs)
                q.put((True, False, None, result))  # Normal completion
            except Exception as e:
                q.put((False, False, traceback.format_exc(), None))  # Error occurred

        q = multiprocessing.Queue()
        p = multiprocessing.Process(target=target_fn, args=(q, *args), kwargs=kwargs)
        p.start()
        p.join(timeout_sec)

        if p.is_alive():
            p.terminate()
            p.join()
            return (False, True, None, None)  # Timeout occurred
        return q.get()  # No timeout, return the result

    return wrapper

