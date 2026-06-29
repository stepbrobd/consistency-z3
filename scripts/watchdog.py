import select
import signal
import subprocess
import sys
import threading
import time

import psutil


def monitor_stdout_writes(pid) -> None:
    try:
        target_process = psutil.Process(pid)
        if not target_process.is_running():
            print(f"process {pid} is not running")
            return

        last_write_time = time.time()
        monitoring = True

        strace_cmd = [
            'strace', '-p', str(pid),
            '-e', 'trace=write',
            '-o', '/dev/stderr',
            '--quiet'
        ]

        def strace_monitor() -> None:
            nonlocal last_write_time, monitoring

            try:
                strace_proc = subprocess.Popen(  # noqa: S603
                    strace_cmd,
                    stderr=subprocess.PIPE,
                    stdout=subprocess.DEVNULL,
                    universal_newlines=True,
                    bufsize=1
                )

                while monitoring and strace_proc.poll() is None:
                    ready, _, _ = select.select([strace_proc.stderr], [], [], 0.1)

                    if ready:
                        line = strace_proc.stderr.readline()
                        if line and ('write(1,' in line or 'write(2,' in line):
                            last_write_time = time.time()
                            print(f"[{time.strftime('%H:%M:%S')}] output detected - resetting timer")

            except Exception as e:
                print(f"error while strace: {e}")
            finally:
                if "strace_proc" in locals():
                    strace_proc.terminate()

        monitor_thread = threading.Thread(target=strace_monitor, daemon=True)
        monitor_thread.start()

        print("monitoring started - waiting for output...")

        while target_process.is_running():
            current_time = time.time()
            silence_duration = current_time - last_write_time

            if silence_duration >= 10.0:
                print(f"no output for {silence_duration:.1f}s - sending SIGINT (Ctrl+C) to PID {pid}")
                try:
                    target_process.send_signal(signal.SIGINT)
                    print(f"SIGINT sent to PID {pid} - should interrupt current operation")

                    # reset timer
                    last_write_time = time.time()

                    # pause and let the process handle interrupt
                    time.sleep(1)

                    if not target_process.is_running():
                        print(f"process {pid} terminated after SIGINT")
                        break
                    else:
                        print(f"process {pid} continuing after SIGINT - monitoring resumed")

                except psutil.NoSuchProcess:
                    print(f"process {pid} terminated")
                    break
                except Exception as e:
                    print(f"error sending SIGINT: {e}")
                    break

            # countdown
            if silence_duration >= 7.0:
                remaining = 10.0 - silence_duration
                print(f"will send SIGINT in {remaining:.1f}s...", end='\r')

            time.sleep(0.5)

        monitoring = False
        print(f"\nprocess {pid} monitoring finished")

    except psutil.NoSuchProcess:
        print(f"process {pid} not found")
    except PermissionError:
        print(f"permission denied - need root to strace PID {pid}")
    except Exception as e:
        print(f"error: {e}")


def main() -> None:
    if len(sys.argv) != 2:
        print("usage: python monitor.py <PID>")
        print("sends SIGINT when no stdout write for 10 sec")
        sys.exit(1)

    try:
        pid = int(sys.argv[1])

        if not psutil.pid_exists(pid):
            print(f"PID {pid} does not exist")
            sys.exit(1)

        monitor_stdout_writes(pid)

    except ValueError:
        print("PID must be an integer")
        sys.exit(1)
    except KeyboardInterrupt:
        print("\nmonitoring interrupted by user")
        sys.exit(0)


if __name__ == "__main__":
    main()
