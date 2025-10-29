// =============================================================================================
// IMPORTS AND DEPENDENCIES (FINAL WORKING VERSION)
// =============================================================================================

use std::{
    env,
    fs::File, 
    path::Path, 
    io::Read,
};

// FIX 1: Import the concrete struct (for UserAuthClient::new(auth))
use dropbox_sdk::default_client::UserAuthDefaultClient as ConcreteClient;
 
// Removed unresolved import: UserAuthClientTrait
use dropbox_sdk::oauth2::Authorization; 
use dropbox_sdk::files::{self, DownloadArg}; 

use tokio; 
use dotenvy; 


// --- UPLOAD FILE HELPER ---
// FIX 3: Use '&dyn UserAuthClient<Authorization>' for the function parameter
async fn upload_file(client: &ConcreteClient, local_path: &Path, dropbox_path: &str) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n⬆️ Starting upload of '{}' to '{}'...", local_path.display(), dropbox_path);
    
    // ... (rest of function body remains the same)
    let mut file = File::open(local_path)?;
    let metadata = file.metadata()?;
    let file_size = metadata.len();
    
    const MAX_SINGLE_UPLOAD: u64 = 150 * 1024 * 1024; 

    if file_size <= MAX_SINGLE_UPLOAD {
        let mut contents = Vec::new();
        file.read_to_end(&mut contents)?;

        let commit_info = files::CommitInfo::new(dropbox_path.to_owned())
            .with_mode(files::WriteMode::Overwrite);

        let upload_arg = files::UploadArg::new(commit_info.path.clone());

        let upload_result = files::upload(client, &upload_arg, &contents)
            .map_err(|e| format!("Upload Error: {}", e))?;

        println!("✅ Single-call upload successful. Revision: {}", upload_result.rev);
    
    } else {
        println!("⚠️ File is large ({} bytes). Chunked upload is required but not implemented in this example.", file_size);
        return Err(Box::from("File size requires chunked upload, which is not implemented in this demo."));
    }

    Ok(())
}


// --- DOWNLOAD FILE HELPER ---
// FIX 4: Use '&dyn UserAuthClient<Authorization>' for the function parameter
async fn download_file(client: &ConcreteClient, dropbox_path: &str, local_path: &Path) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n⬇️ Starting download of '{}' to '{}'...", dropbox_path, local_path.display());

    let arg = DownloadArg::new(dropbox_path.to_owned());

    let download_result = files::download(client, &arg, None, None)
        .map_err(|e| format!("Download Error: {}", e))?;

    let dropbox_sdk::HttpRequestResult { result: _, body, content_length: _ } = download_result;
    // The result is already of the expected type and does not need reassignment.
    
    let mut local_file = File::create(local_path)?;

    let mut body = body.ok_or("Download body is None")?;
    std::io::copy(&mut body, &mut local_file)?;

    println!("✅ Download successful.");

    Ok(())
}


// --- MAIN APPLICATION ---
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // ... (Authentication setup)
    dotenvy::dotenv().ok();

    let app_key: String = env::var("DROPBOX_APP_KEY").expect("Missing DROPBOX_APP_KEY in .env");
    let app_secret: String = env::var("DROPBOX_APP_SECRET").expect("Missing DROPBOX_APP_SECRET in .env");
    let refresh_token: String = env::var("DROPBOX_REFRESH_TOKEN").expect("Missing DROPBOX_REFRESH_TOKEN in .env");

    let auth = Authorization::from_client_secret_refresh_token(
        app_key, 
        app_secret, 
        refresh_token
    );
    let client = ConcreteClient::new(auth); // Ensure the client is configured with an HTTP client

    println!("🔑 Successfully initialized Dropbox client.");

    // The functions below need a reference to a trait object (&dyn ...)
    // which is why we pass a reference to the concrete client (&client)

    // --- LIST FOLDER ---
    // The main list folder call also requires the concrete client to be used
    let list_result = files::list_folder(&client, &files::ListFolderArg::new("".to_string()))
            .map_err(|e| format!("List Folder Error: {}", e))?;

    println!("\n--- Dropbox Root Folder Contents ---");
    for entry in list_result.entries {
        match entry {
            dropbox_sdk::files::Metadata::File(file_metadata) => println!("- {}", file_metadata.name),
            dropbox_sdk::files::Metadata::Folder(folder_metadata) => println!("- {}", folder_metadata.name),
            _ => println!("- [Unknown Metadata Type]"),
        }
    }
    println!("------------------------------------");

    // --- UPLOAD FILE ---
    let local_file_path = Path::new("test_upload.txt");
    if !local_file_path.exists() {
        std::fs::write(local_file_path, "Hello, Dropbox! This is a test file from Rust.")?;
    }
    let dropbox_destination_path = "/rust_test/uploaded_file.txt"; 

    match upload_file(&client, local_file_path, dropbox_destination_path).await {
        Ok(_) => println!("Upload routine finished."),
        Err(e) => eprintln!("Upload routine failed: {}", e),
    }

    // --- DOWNLOAD FILE ---
    let download_source_path = "/rust_test/uploaded_file.txt";
    let local_destination_path = Path::new("downloaded_file.txt");

    match download_file(&client, download_source_path, local_destination_path).await {
        Ok(_) => println!("Download routine finished. Check your project folder for '{}'.", local_destination_path.display()),
        Err(e) => eprintln!("Download routine failed: {}", e),
    }

    Ok(())
}