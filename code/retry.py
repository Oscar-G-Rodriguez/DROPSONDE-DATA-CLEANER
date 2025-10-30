import shutil
from pathlib import Path
import os
import stat

BASE_DIR = Path(__file__).resolve().parent.parent
DONE_ROOT = BASE_DIR / "DATA" / "Done"

def on_rm_error(func, path, exc_info):
    # change file permission and retry delete
    os.chmod(path, stat.S_IWRITE)
    func(path)

def is_year_folder(p: Path) -> bool:
    return p.is_dir() and p.name.isdigit() and len(p.name) == 4

def empty_all_years(dry_run: bool = False):
    """
    iterate over all year directories in DONE_ROOT
    and delete everything inside them, keeping the year folder itself.
    """
    for year_dir in DONE_ROOT.iterdir():
        if is_year_folder(year_dir):
            children = list(year_dir.iterdir())
            if not children:
                print(f"[info] already empty: {year_dir}")
                continue

            print(f"clearing contents of {year_dir}")
            for child in children:
                if dry_run:
                    print(f"[dry-run] would delete: {child}")
                    continue

                if child.is_file():
                    print(f"deleting file: {child}")
                    try:
                        child.unlink()
                    except PermissionError:
                        on_rm_error(os.remove, str(child), None)
                else:
                    print(f"removing directory: {child}")
                    shutil.rmtree(child, onerror=on_rm_error)
            print(f"[done] emptied: {year_dir}")
        else:
            # skip anything that isn't a year directory
            continue


empty_all_years(dry_run=False)