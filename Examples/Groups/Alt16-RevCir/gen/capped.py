"""Run a Python script under a memory cap and a time limit (Windows).

    python capped.py <megabytes> <seconds> script.py [args ...]

The script runs in a job object whose memory limit makes allocations fail
(a MemoryError in the script) once the job has committed <megabytes>, at
below-normal priority, and the whole job is killed after <seconds> of wall
time.  The exit code is the script's, or 124 on a timeout.  Searches in
this folder are run through it so that a runaway frontier cannot take the
machine down.
"""
import ctypes
import subprocess
import sys
from ctypes import wintypes

JOB_OBJECT_LIMIT_PROCESS_MEMORY = 0x0100
JOB_OBJECT_LIMIT_JOB_MEMORY = 0x0200
JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE = 0x2000
EXTENDED_LIMIT_INFORMATION = 9
BELOW_NORMAL_PRIORITY_CLASS = 0x4000


class BasicLimits(ctypes.Structure):
    _fields_ = [
        ('PerProcessUserTimeLimit', ctypes.c_int64),
        ('PerJobUserTimeLimit', ctypes.c_int64),
        ('LimitFlags', wintypes.DWORD),
        ('MinimumWorkingSetSize', ctypes.c_size_t),
        ('MaximumWorkingSetSize', ctypes.c_size_t),
        ('ActiveProcessLimit', wintypes.DWORD),
        ('Affinity', ctypes.c_size_t),
        ('PriorityClass', wintypes.DWORD),
        ('SchedulingClass', wintypes.DWORD),
    ]


class IoCounters(ctypes.Structure):
    _fields_ = [(name, ctypes.c_uint64) for name in (
        'ReadOperationCount', 'WriteOperationCount', 'OtherOperationCount',
        'ReadTransferCount', 'WriteTransferCount', 'OtherTransferCount')]


class ExtendedLimits(ctypes.Structure):
    _fields_ = [
        ('BasicLimitInformation', BasicLimits),
        ('IoInfo', IoCounters),
        ('ProcessMemoryLimit', ctypes.c_size_t),
        ('JobMemoryLimit', ctypes.c_size_t),
        ('PeakProcessMemoryUsed', ctypes.c_size_t),
        ('PeakJobMemoryUsed', ctypes.c_size_t),
    ]


def main():
    if len(sys.argv) < 4:
        sys.exit(__doc__)
    megabytes, seconds = int(sys.argv[1]), float(sys.argv[2])
    kernel32 = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel32.CreateJobObjectW.restype = wintypes.HANDLE
    kernel32.CreateJobObjectW.argtypes = [ctypes.c_void_p, wintypes.LPCWSTR]
    kernel32.SetInformationJobObject.argtypes = [
        wintypes.HANDLE, ctypes.c_int, ctypes.c_void_p, wintypes.DWORD]
    kernel32.AssignProcessToJobObject.argtypes = [
        wintypes.HANDLE, wintypes.HANDLE]
    kernel32.TerminateJobObject.argtypes = [wintypes.HANDLE, wintypes.UINT]

    job = kernel32.CreateJobObjectW(None, None)
    if not job:
        raise ctypes.WinError(ctypes.get_last_error())
    limits = ExtendedLimits()
    limits.BasicLimitInformation.LimitFlags = (
        JOB_OBJECT_LIMIT_PROCESS_MEMORY | JOB_OBJECT_LIMIT_JOB_MEMORY
        | JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE)
    limits.ProcessMemoryLimit = megabytes * 1024 * 1024
    limits.JobMemoryLimit = megabytes * 1024 * 1024
    if not kernel32.SetInformationJobObject(
            job, EXTENDED_LIMIT_INFORMATION, ctypes.byref(limits),
            ctypes.sizeof(limits)):
        raise ctypes.WinError(ctypes.get_last_error())

    proc = subprocess.Popen([sys.executable, '-u'] + sys.argv[3:],
                            creationflags=BELOW_NORMAL_PRIORITY_CLASS)
    if not kernel32.AssignProcessToJobObject(job, int(proc._handle)):
        proc.kill()
        raise ctypes.WinError(ctypes.get_last_error())
    try:
        code = proc.wait(timeout=seconds)
    except subprocess.TimeoutExpired:
        kernel32.TerminateJobObject(job, 124)
        proc.wait()
        print('capped.py: killed after %g s' % seconds, file=sys.stderr)
        code = 124
    sys.exit(code)


if __name__ == '__main__':
    main()
