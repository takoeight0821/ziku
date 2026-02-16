#!/usr/bin/env python3
import os
import subprocess
import sys
import glob

def run_ziku(file_path, mode):
    """Runs ziku with the specified mode and returns stdout, stderr, and exit code."""
    cmd = ["lake", "exe", "ziku", mode, file_path]
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            check=False
        )
        return result.stdout.strip(), result.stderr.strip(), result.returncode
    except Exception as e:
        return "", str(e), -1

def main():
    test_dir = "tests/golden/ir-eval/success"
    if not os.path.exists(test_dir):
        print(f"Error: Directory {test_dir} not found.")
        sys.exit(1)

    ziku_files = sorted(glob.glob(os.path.join(test_dir, "*.ziku")))
    
    passed = 0
    failed = 0
    errors = 0
    
    print(f"Found {len(ziku_files)} tests in {test_dir}")
    print("-" * 60)
    print(f"{'Test Name':<40} | {'Status':<10}")
    print("-" * 60)

    for file_path in ziku_files:
        test_name = os.path.basename(file_path)
        
        # Run Small Step (--eval)
        s_out, s_err, s_code = run_ziku(file_path, "--eval")
        
        # Run Big Step (--big-step)
        b_out, b_err, b_code = run_ziku(file_path, "--big-step")
        
        if s_code != 0:
            # If small step fails, we probably shouldn't expect big step to pass yet, 
            # or it's a broken test.
            # But let's check if they agree on failure.
            pass

        if b_code != 0 and s_code == 0:
             print(f"{test_name:<40} | ERROR (Big Step crash)")
             errors += 1
             continue
        
        if s_out == b_out:
            print(f"{test_name:<40} | PASS")
            passed += 1
        else:
            print(f"{test_name:<40} | FAIL")
            failed += 1
            # Print diff for the first few failures or if requested
            # print(f"Expected:\n{s_out}\nGot:\n{b_out}\n")

    print("-" * 60)
    print(f"Total: {len(ziku_files)}")
    print(f"Passed: {passed}")
    print(f"Failed: {failed}")
    print(f"Errors: {errors}")

    if failed > 0 or errors > 0:
        sys.exit(1)

if __name__ == "__main__":
    main()
