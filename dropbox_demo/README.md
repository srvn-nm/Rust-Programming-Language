# Dropbox Rust Demo

This project is a comprehensive demonstration of how to connect a Rust application to the Dropbox API using the `dropbox-sdk` crate. It implements the modern, secure **Refresh Token** authentication flow to ensure continuous, long-term access without requiring manual re-authentication after the short-lived access token expires.

This demo successfully implements:

1. Secure configuration using environment variables (`.env`).
2. Automatic token refreshing for long-term access.
3. Listing the contents of the Dropbox root folder.
4. Uploading a file (up to 150MB) to a specified Dropbox path.

---

## 🛠️ Setup and Installation

### Prerequisites

* **Rust and Cargo:** Installed on your system.
* **Dropbox Developer App:** A [Scoped App] created in the Dropbox App Console.
* **App Credentials:** You must have the `App key` (Client ID) and `App secret` from your Dropbox app settings.

### 1. Initialize Project and Dependencies

1. **Create Project and Navigate:**

    ```bash
    cargo new dropbox_demo
    cd dropbox_demo
    ```

2. **Edit `Cargo.toml`:** Add the necessary crates for the SDK, environment variables, and asynchronous runtime.

    ```toml
    # Cargo.toml
    [dependencies]
    dropbox-sdk = "0.19"
    dotenvy = "0.15"
    tokio = { version = "1", features = ["full"] }
    ```

### 2. Configure Dropbox App Permissions (Scopes)

The Dropbox API uses **scopes** to grant explicit permissions. You must enable these in the App Console for any API call you make.

1. **Navigate to Permissions:** Go to your app in the [Dropbox App Console] and click the **"Permissions"** tab.
2. **Enable Required Scopes:** Check the boxes for the necessary permissions:
    * ✅ **`files.metadata.read`**: Required for reading folder contents (`files/list_folder`).
    * ✅ **`files.content.write`**: Required for uploading files (`files/upload`).
3. **Save Changes:** Click the **"Submit"** or **"Apply"** button at the bottom of the page.

### 3. Generate the Refresh Token

Because you changed permissions, and to enable the long-term flow, you must perform the OAuth process to generate a new **Refresh Token**.

1. **Register Redirect URI:** In the **Settings** tab of your App Console, under **"OAuth 2"**, add `http://localhost:8000` to the **Redirect URIs** list.

2. **Authorization URL:** Paste this URL into your browser, replacing the bracketed placeholders, and hit Enter. The crucial parameter is `token_access_type=offline`.

    ```url
    [https://www.dropbox.com/oauth2/authorize?client_id=](https://www.dropbox.com/oauth2/authorize?client_id=)[YOUR_APP_KEY]&response_type=code&token_access_type=offline&redirect_uri=http://localhost:8000
    ```

3. **Capture Authorization Code:** Authorize the app. You will be redirected to `http://localhost:8000/?code=...`. **Copy the value of the `code` parameter.**

4. **Exchange for Tokens (Using `curl`):** Use the following command in your terminal to exchange the authorization code for the Refresh Token. **Use your App Key and Secret here.**

    ```bash
    curl -X POST [https://api.dropboxapi.com/oauth2/token](https://api.dropboxapi.com/oauth2/token) \
    -u "[YOUR_APP_KEY]:[YOUR_APP_SECRET]" \
    -d grant_type=authorization_code \
    -d code=[AUTH_CODE_FROM_STEP_3] \
    -d redirect_uri=http://localhost:8000
    ```

5. **Extract and Save Token:** The JSON response will contain a long string labeled **`refresh_token`**.

### 4. Configure Environment Variables

Create a file named `.env` in your project root (`./dropbox_demo/.env`) and paste your credentials and the generated refresh token.

.env
DROPBOX_APP_KEY="[YOUR_APP_KEY]" DROPBOX_APP_SECRET="[YOUR_APP_SECRET]" DROPBOX_REFRESH_TOKEN="[YOUR_GENERATED_REFRESH_TOKEN_HERE]"

---

## 💻 Rust Application Code (`src/main.rs`)

Replace the contents of `src/main.rs` with the following complete code block.

```rust
use std::{env, fs::File, path::Path, io::Read};
use dropbox_sdk::default_client::UserAuthClient;
use dropbox_sdk::oauth2::Authorization;
use dropbox_sdk::client_trait::UserAuthClientTrait;
use dropbox_sdk::files::{self, CommitInfo};
use tokio;

// Helper function to upload a file to Dropbox
async fn upload_file(client: &UserAuthClient<Authorization>, local_path: &Path, dropbox_path: &str) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n⬆️ Starting upload of '{}' to '{}'...", local_path.display(), dropbox_path);
    
    // 1. Open the local file and get its size
    let mut file = File::open(local_path)?;
    let metadata = file.metadata()?;
    let file_size = metadata.len();
    
    // Define the maximum size for a simple single-call upload (150MB)
    const MAX_SINGLE_UPLOAD: u64 = 150 * 1024 * 1024; 

    // 2. Perform the upload
    if file_size <= MAX_SINGLE_UPLOAD {
        // Single call upload
        let mut contents = Vec::new();
        file.read_to_end(&mut contents)?;

        let arg = files::CommitInfo::new(dropbox_path.to_owned())
            .with_mode(files::WriteMode::Overwrite);

        let upload_result = client.files_upload(arg, contents)
            .await
            .map_err(|e| format!("Upload Error: {}", e))?;

        println!("✅ Single-call upload successful. Revision: {}", upload_result.unwrap().rev);
    
    } else {
        // NOTE: For large files, implement the chunked upload session flow here.
        println!("⚠️ File is large ({} bytes). Chunked upload is required but not implemented in this example.", file_size);
        return Err(Box::from("File size requires chunked upload, which is not implemented in this demo."));
    }

    Ok(())
}


#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. Load the .env file
    dotenvy::dotenv().ok();

    // 2. Load credentials
    let app_key: String = env::var("DROPBOX_APP_KEY").expect("Missing DROPBOX_APP_KEY in .env");
    let app_secret: String = env::var("DROPBOX_APP_SECRET").expect("Missing DROPBOX_APP_SECRET in .env");
    let refresh_token: String = env::var("DROPBOX_REFRESH_TOKEN").expect("Missing DROPBOX_REFRESH_TOKEN in .env");

    // 3. Initialize Authorization and Client
    // This is the core of the refresh token flow.
    let auth = Authorization::from_client_secret_refresh_token(
        app_key, 
        app_secret, 
        refresh_token
    );
    let client = UserAuthClient::new(auth);

    println!("🔑 Successfully initialized Dropbox client.");

    // --- LIST FOLDER (Requires files.metadata.read scope) ---
    let list_result = client.files_list_folder(&files::ListFolderArg::new("".to_string()))
        .await
        .map_err(|e| format!("List Folder Error: {}", e))?;

    println!("\n--- Dropbox Root Folder Contents ---");
    for entry in list_result.unwrap().entries {
        println!("- {}", entry.name());
    }
    println!("------------------------------------");

    // --- UPLOAD FILE (Requires files.content.write scope) ---
    // Create a dummy file if it doesn't exist
    let local_file_path = Path::new("test_upload.txt");
    if !local_file_path.exists() {
        std::fs::write(local_file_path, "Hello, Dropbox! This is a test file from Rust.")?;
    }
    let dropbox_destination_path = "/rust_test/uploaded_file.txt"; // Target path in Dropbox

    match upload_file(&client, local_file_path, dropbox_destination_path).await {
        Ok(_) => println!("\nUpload function completed successfully."),
        Err(e) => eprintln!("\nUpload failed: {}", e),
    }

    Ok(())
}
